(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts MpiClient.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_grow
     P_mpi_copy P_mpi_shift_l P_mpi_cmp P_mpi_lset P_mpi_mul_int_W P_mpi_core_bitlen P_mpi_core_shift_r P_mpi_divmod_stmt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_div_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_mod_mpi () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.bool"; "ModP.Walk.ALIAS"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.LNull"; "ModP.Walk.es"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.P.PImg.psegs"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Spec.MpiClient.cstate"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.AEvt.MOK"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "OSSVerify.KrLib.Spec.MpiVal.mpd_abs"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_mpi_addsub.mpi_binop_post"; "OSSVerify.KrLib.P.P_mpi_divmod_stmt.mod_mpi_R"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "OSSVerify.KrLib.Lib.MpiCoreAux.limb32"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"].


Definition P_MPI_MOD_MPI' : Z := 0x2093c.

Section ModP.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr psegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Variable MSF : Z.
  Hypothesis MSFE : MSF = P_MEMSET_FUNC.
  (* [comment removed for export] *)
  Hypothesis HDIV : mpi_div_mpi_stmt psegs L HI P_MPI_DIV_MPI MSF.
  Hypothesis HCMP : mpi_cmp_mpi_stmt psegs P_MPI_CMP_MPI.
  Hypothesis HAS : add_sub_mpi_stmt psegs L HI P_ADD_SUB_MPI MSF.

  Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST psegs L HI) (LB : list blk) (dR dA dB : mpd) (lo : Z).
  Hypothesis HH0 : HEAP psegs L HI h LB m mo.
  Hypothesis MR0 : mpd_at psegs m LB dR.
  Hypothesis MA0 : mpd_at psegs m LB dA.
  Hypothesis MB0 : mpd_at psegs m LB dB.
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
  Hypothesis WRR : mpd_writable L LB (bv_unsigned sp) (heap_top psegs L HI h) dR.
  Hypothesis RLO : md_own dR <> LNull -> md_p dR + 4 * md_n dR <= lo \/ bv_unsigned sp <= md_p dR.
  Hypothesis ST0 : stk psegs m lo (bv_unsigned sp).
  Hypothesis SLO : lo <= bv_unsigned sp - 576 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top psegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv psegs m.
  Hypothesis SOK0 : statics_ok psegs L m.
  Hypothesis CA : const_at L MSF 8.

  Notation SP := (bv_unsigned sp).
  Notation SPc := (bv_unsigned sp + -32).
  Notation POST := (mpi_binop_post psegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dR (mod_mpi_R LB dR dA dB) lo m mo).

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
  Notation CST := (cstate psegs L HI h LB mo m SP lo SPc dR es).
  Local Ltac mc_inst H :=
    exact (H psegs L HI HLS DIMG HND IMGC SW ROIMG h LB mo m SP lo SPc dR es
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

  Notation SPF' := (Z_to_bv 64 (bv_unsigned sp + -32)).

  Notation FRM j8 := ([(SPc, [CB 8 j8; C8 s1; C8 s0; C8 ra])] : list (Z * list cell)).

  Lemma cs_parts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pmq,P,(21.&40.)(22.(21.&8.))Pmoq,$23.Phq,(24.$25.VL,VHI,)PLBq,(26.$27.)PdW,$1<.PCS,(26.(>.$4.(26.$28.)))P,(29.$25.VL,VHI,Vh,VLB,Vmo,Vm,(9.&40.Vsp,)Vlo,(8.(9.&40.Vsp,)-20.)VdR,$20.R6.R5.R4.R3.(2:.$1<.)R2.(2:.$27.)R1.(2:.(>.$4.(26.$28.))))(0.(2;.$25.VL,VHI,R5.R4.R7.R6.)(0.(3.$4.(2<.$25.VL,VHI,R5.)(2<.$25.VL,VHI,Vh,))(0.(2=.Vmo,R6.)(0.(2>.$25.VL,R7.)(0.(2?.$25.R7.)(0.(30.$25.R7.Vlo,(8.(9.&40.Vsp,)-20.))(0.(13.(>.$4.(26.$28.))Lac,(>.$4.(26.$28.))(31.$25.R8.(15.$4.(26.$28.)R1.)(16.$4.(26.$28.)R1.))R2.)(32.R6.))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq dW CS CS_.
    flat constr:(CS_) 21%nat. flclear CS_. intros HH HTc MF LOK SA LA MW WOK EXOK SUB COV FRS EXT PX SOK MI ST CH CHS CXH CXS.
    split; [exact HH|]. split; [exact HTc|]. split; [exact MF|]. split; [exact SOK|]. split; [exact MI|]. split; [exact ST|].
    split; [exact CH|]. exact (heap_mok _ _ HI _ _ _ _ HH).
  Qed.

  Lemma ext_facts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pmq,P,(21.&40.)(22.(21.&8.))Pmoq,$23.Phq,(24.$25.VL,VHI,)PLBq,(26.$27.)PdW,$1<.PCS,(26.(>.$4.(26.$28.)))Pd,$1<.P,(29.$25.VL,VHI,Vh,VLB,Vmo,Vm,(9.&40.Vsp,)Vlo,(8.(9.&40.Vsp,)-20.)VdR,$20.R7.R6.R5.R4.(2:.$1<.)R3.(2:.$27.)R2.(2:.(>.$4.(26.$28.))))P,(=.$1<.R2.$20.)(0.(33.$25.R9.R6.R3.)(0.(1=.VL,R6.Vlo,(2.R3.)+10.)(0.P,(3.$:.(;.R3.)$<.)(1=.VL,R7.Vlo,(10.R4.)(11.+4.(12.R4.)))(0.P,(1>.(3.$:.(;.R3.)$1?.))(6.(7.(8.(10.R4.)(11.+4.(12.R4.)))Vlo,)(7.(8.(9.&40.Vsp,)-20.)(10.R4.)))(0.P,(3.$:.(;.R3.)$<.)(0.(1.=(10.R4.))(7.+1.(12.R4.)))(6.(7.(8.(2.R3.)+10.)Vlo,)(7.(9.&40.Vsp,)(2.R3.))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq dW CS d CS_ IN.
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ _ CS_ IN)) 6%nat. intros ME CRE CREL LE HFE ASE.
    split; [exact ME|]. split; [exact CRE|]. split; [exact CREL|]. split; [exact LE|]. split; [| exact ASE]. intros O. flat constr:((HFE O)) 4%nat. intros P0 _ _ N1. auto.
  Qed.
  Lemma es_at : Forall (fun e => mpd_at psegs m LB e) es.
  Proof. unfold es. destruct ALIAS; [constructor; [exact MB0| constructor]| constructor; [exact MA0| constructor; [exact MB0| constructor]]]. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L21887662552.110L33510041944.110L39941600002.109L41564619544.108L66083662040.11000000400800M00Q00US2spS2spS1L3HLS2sp2lo3SLO3SPBS2spS2sp". (* [comment removed for export] *)
  Lemma L_epi : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pmq,P,(21.&40.)(22.(21.&8.))Pmoq,$23.Phq,(24.$25.VL,VHI,)PLBq,(26.$27.)PdW,$1<.Pj8,(26.(21.&8.))Pr,$4.Pxra,(21.&40.)Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Pa1,(21.&40.)Pa2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Px8,(21.&40.)Px9,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)P,(29.$25.VL,VHI,Vh,VLB,Vmo,Vm,(9.&40.Vsp,)Vlo,(8.(9.&40.Vsp,)-20.)VdR,$20.R18.R17.R16.R15.(2:.$1<.)R14.(2:.$27.)(34.(>.$4.(26.$28.))(?.$4.(26.$28.)(8.(9.&40.Vsp,)-20.)(34.$28.(35.#8.R13.)(34.$28.(36.Vs1,)(34.$28.(36.Vs0,)(34.$28.(36.Vra,)(2:.$28.))))))(2:.(>.$4.(26.$28.))))(2:.(>.$4.(26.$28.))))P,(0.(1.(37.(18.+2.+1?.))R13.)(7.R13.=))P,P,(3.$4.R14.=)(0.(7.=(38.R17.))(1.(38.R17.)(39.VdB,)))(3:.$25.R1:.(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.R14.(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,R13.R12.R11.R9.R8.(3?.&40.R15.)R10.R?.R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(3?.&40.+20:38.)Vfc,(40.(21.&40.))R1;.(41.$25.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ Hr HV.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((mc_final _ _ _ _ _ _ _ _ CS_ ltac:(constructor))) 11%nat. intros HH HT MF MW OUT BK PX SOK MI ST CH.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CHR. cbn [fst snd] in CHR. clear CH.
    zstep. zstep. zstep.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L16075584458.137L1636212821.15  L22700177074.2  L2397676628.0   L29010566049.154L29956516996.0  L36253289358.15 L45290767137.15 L50403522089.17 L59308587409.1  L59308628304.1  L59308943857.3  L65510790704.138L6627431889.9   L7186539239.145 L7190718996.174 L7262017168.174 00000100L00S00T00U00V00c01D01E01I01M01W01f02@02k03V03hFS1L2HI2sp1h4HTOP2hq3SPB3HTcS2dB2dWSFSS1L2sp2lo3SLOS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPFS2HrS2K1S2vb2dW2VRS2sp2vb1D2dW2VRS2dB2vb1D2dW3VBE3VBA2VR2K0S1L3HLS2sp2dB2lo3SLO3ACL2vb1D2dW2VR3SPB3ACPS1L3HLS2sp2dB2lo3SLO3ACL2vb1D2dW2VR3SPB3ACPS2sp2dB2vb1D2dW2VR". (* [comment removed for export] *)
  Lemma L_loopB : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pvb,$4.PD,$42.Pmq,P,(21.&40.)(22.(21.&8.))Pmoq,$23.Phq,(24.$25.VL,VHI,)PLBq,(26.$27.)PdW,$1<.Pj8,(26.(21.&8.))Pxra,(21.&40.)Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Pa0,(21.&40.)Pa1,(21.&40.)Pa2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)P,(29.$25.VL,VHI,Vh,VLB,Vmo,Vm,(9.&40.Vsp,)Vlo,(8.(9.&40.Vsp,)-20.)VdR,$20.R16.R15.R14.R13.(2:.$1<.)R12.(2:.$27.)(34.(>.$4.(26.$28.))(?.$4.(26.$28.)(8.(9.&40.Vsp,)-20.)(34.$28.(35.#8.R11.)(34.$28.(36.Vs1,)(34.$28.(36.Vs0,)(34.$28.(36.Vra,)(2:.$28.))))))(2:.(>.$4.(26.$28.))))(2:.(>.$4.(26.$28.))))P,(3.$4.(38.VdB,)R19.)P,(1.=R1:.)P,(3.$4.R1;.(39.VdB,))P,(0.(7.=(38.R16.))(1.(38.R16.)(11.(43.R1;.)R1<.)))(3:.$25.R1:.(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.R15.(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,R14.R13.R12.(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))R11.R10.R?.R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(3?.&40.+20:1<.)Vfc,(40.(21.&40.))R1;.(41.$25.)))")
(* [comment removed for export] *).
  Proof.
    intros vb D. induction D as [|D IH]; intros until t6; intros CS_ VBE VB0 VBA VR; [exfalso; clear - VR; lia|].
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_parts _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW NSW EA WR LW CRW CRWL HFW ASW WA8.
    flat constr:((ext_facts _ _ _ _ _ _ dB CS_ opndB)) 6%nat. intros MB CRB_ CRBL_ LOB HFB ASB.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof HCMP as SPC. unfold mpi_cmp_mpi_stmt, P_MPI_CMP_MPI in SPC.
    eapply aevtM_cut_evt; [exact MK| eapply SPC with (dX := dW) (dY := dB) (LB := LBq); try eassumption; try reflexivity|].
    all: try (rewrite ?EA; reflexivity).
    1:{ intros O. flat constr:((HFW O)) 2%nat. intros P0 _. exact P0. }
    1:{ intros O. flat constr:((HFB O)) 2%nat. intros P0 _. exact P0. }
    clear SPC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO. destruct_exs PO.
    flat constr:(PO) 4%nat. flclear PO. intros -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x20a28)) with (Z_to_bv 64 0x20a28) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      replace (ret_pc (Z_to_bv 64 0x20a18)) with (Z_to_bv 64 0x20a18) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      flat constr:(RR) 2%nat. flclear RR. intros R1 FLt4. flat constr:(FLt4) 4%nat. flclear FLt4. intros KA KP KF KN.
      assert (CS2 : CST m2 mo2 h2 LB2 [] dW2 [] (FRM j8) []).
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
  Section ScanR.
    Variables (mq : mem) (moq : Model) (pR nR : Z) (zs : list word).
    Hypothesis MKq : MOK moq.
    Hypothesis HXR : bytes_at psegs mq pR (u32s zs).
    Hypothesis LXR : Z.of_nat (length zs) = nR.
    Hypothesis BNR : 0 <= nR <= 10000.
    Hypothesis PR4 : nR = 0 \/ 0 < pR /\ pR mod 4 = 0.
    Variables (xra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word).
    Hypothesis KZ : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "P,(3.$4.(44.Vzs,VnR,)=)Pwa0,(21.&40.)Pwa1,(21.&40.)Pwa2,(21.&40.)(3:.$25.Vmoq,(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.Vxra,(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,Vt0,Vt1,Vt2,(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))R3.R2.R1.Va3,Va4,Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(3?.&40.+20:1<.)Vfc,(40.(21.&40.))Vmq,(41.$25.)))")
(* [comment removed for export] *).
    Hypothesis KNZ : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pr,$4.P,(0.(7.+1.R1.)(7.R1.VnR,))P,(1>.(3.$4.(45.Vzs,(46.(47.R2.+1.)))=))Pwa1,(21.&40.)Pwa2,(21.&40.)(3:.$25.Vmoq,(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.Vxra,(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,Vt0,Vt1,Vt2,(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))(3?.&40.R5.)R2.R1.Va3,Va4,Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(3?.&40.+209?4.)Vfc,(40.(21.&40.))Vmq,(41.$25.)))")
(* [comment removed for export] *).
    Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L11014201954.106L13498927707.106L13806697134.104L22386736417.101L22388914092.98 L23917382008.106L23970764156.105L24065293318.106L27579345746.106L31326834835.106L40340721375.106L42468637227.103L54425554052.10200000J00d01503Y06006N06i07=07e08B08_09309JS2sp2pR2nR2zs1k1r2Hk2Hr2wyS2sp2pR2nR2zs1k1r2Hk2Hr2wyS2sp2pR2zs1k1r2HkS1L2HI2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m2mo1h2LB2dR2dA2dB2lo2mq3moq2pR2nR2zs3LXR3PR43xra2t02t12t22a32a42a52a62a72t32t42t52t61k1r3wa22Hk2Hr2NYS1L2HI2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m2mo1h2LB2dR2dA2dB2lo2mq3moq2pR2nR2zs3xra2t02t12t22a32a42a52a62a72t32t42t52t61r3wa22Hk2HrS2sp2pR2nR2zs3PR41k1r2Hk2Hr2wyS2sp2nR2zs3BNR1k1r2Hk2Hr2wyS2sp2pR2zs1k1r2Hk2wyS2sp2pR2nR2zs3PR41k1r2Hk2Hr2wy3LYr2K12K2S2sp2pR2nR2zs1k1r2Hk2Hr2wy2K2S2sp2pR2nR2zs1k1r2Hk2Hr2wy2K2S2sp2pR2zs1k1r2Hk2wyS2sp2pR2nR2zs1k1r2Hk2Hr". (* [comment removed for export] *)
    Lemma L_scanR : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pk,$42.Pr,$4.Pwa0,(21.&40.)Pwa1,(21.&40.)Pwa2,(21.&40.)P,(3.$42.(46.R4.)R5.)P,(0.(7.+1.R5.)(7.R5.VnR,))P,(3.$4.(44.Vzs,VnR,)(44.Vzs,R6.))P,(3.(21.&40.)R6.(3?.&40.R7.))P,(3.(21.&40.)R6.(3?.&40.(47.(8.VpR,(11.+4.R8.))+4.)))(3:.$25.Vmoq,(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.Vxra,(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,Vt0,Vt1,Vt2,(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))R8.R7.R6.Va3,Va4,Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(3?.&40.+209=<.)Vfc,(40.(21.&40.))Vmq,(41.$25.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros r wa0 wa1 wa2 Hk Hr INV -> ->; [lia|].
      destruct (nth_error zs (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; lia].
      pose proof (u32ro_read psegs mq pR zs (r - 1) wy _ HXR NY ltac:(lia) eq_refl) as RDY.
      zstep. clear RDY. pose proof (limb32_of_read zs r wy NY) as LYr.
      pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(lia)) as By.
      zstep; if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
      - assert (NZ : limb32 zs (Z.to_nat (r - 1)) <> 0) by (rewrite LYr; intros E; apply K1; rewrite E; reflexivity).
        apply (KNZ r); [lia| exact NZ].
      - apply (proj1 (sxz_zero_iff _ By)) in K1.
        zstep. zstep. zstep; if_cases K2; zify_cond K2.
        + eapply (IH (r - 1)); [lia| lia| rewrite INV; apply lval_drop_zero; [lia| rewrite LYr; exact K1]| f_equal; lia| f_equal; lia].
        + zstep. apply KZ. rewrite INV, (lval_drop_zero zs r) by (try lia; rewrite LYr; exact K1). replace (r - 1) with 0 by lia. apply lval_0.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End ScanR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0@L11011115746.132L1386329383.163 L14285141392.178L1636212821.15  L2397676628.0   L24897143244.3  L29010566049.132L29956516996.0  L34485914988.1  L35246701604.2  L36253289358.15 L36950928818.2  L36967796881.1  L37270831529.3  L37467816751.3  L38820185278.123L38820185532.133L38822213050.125L41417954122.127L42378830594.124L42627901610.2  L44606970405.3  L45290767137.15 L46936163616.4  L50403522089.17 L53221873978.3  L5367509086.136 L54431941911.133L5607952496.2   L56238803769.135L56530236030.2  L59308546259.3  L59308588187.1  L59308628304.4  L59308628566.1  L62502499107.1  L62542020947.2  L7186539239.149 L7190718996.178 L7402790423.126 L9944873874.134 00000D00E00T00o01001401Y01Z01^01e02202302702@02K02^02_03203A03T03\03g04H04T04U04`05405H05O05c05k06506906E06I06M06T07E08608E08YS2sp2dR2dW4WB161r2HrFS2sp2dR2dW4WB16S1L2HI2sp1h4HTOP2hq3SPB3HTcSS2dWS2sp2dR2dW3SPB4POSW3HNW4WB163PR41r2HrSS2dWS2dB2dWS1L2sp2lo3SLOSS2dWS2dW1q2HqS2dW3SGW2K2S2sp2dR2dW3HNW4WB16FS2sp2dR2dW3HNW4WB16S2sp2dR2dW4WB16S2sp2dR2dW3HNW4WB16S2vb3VB0S2dW3SGW2K2S1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2dW1b1l3HLWFS2dW3HNW2K0S2sp2dR2dW4WB161r2HrS2sp2dR2dW4WB161r2HrS2dW2APS2sp2dR2dW4WB161r2HrS2dW3HNWS2dW2K02N0S2HxS2dW1r2Hr2K1S2K3S2dWS2dW2APS1L3HLS2sp2dR2lo3SLO3ACL2dW3SPB3ACP4POSW4WB163PR4S1L3HLS2sp2dR2lo3SLO3ACL2dW3SPB3ACP4POSW4WB163PR4S2sp2dR2dW4WB16S2sp2dR2dW4WB161r2Hr". (* [comment removed for export] *)
  Lemma L_loopA_step : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pvb,$4.Pmq,P,(21.&40.)(22.(21.&8.))Pmoq,$23.Phq,(24.$25.VL,VHI,)PLBq,(26.$27.)PdW,$1<.Pj8,(26.(21.&8.))Pxra,(21.&40.)Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Pa0,(21.&40.)Pa1,(21.&40.)Pa2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)P,(29.$25.VL,VHI,Vh,VLB,Vmo,Vm,(9.&40.Vsp,)Vlo,(8.(9.&40.Vsp,)-20.)VdR,$20.R16.R15.R14.R13.(2:.$1<.)R12.(2:.$27.)(34.(>.$4.(26.$28.))(?.$4.(26.$28.)(8.(9.&40.Vsp,)-20.)(34.$28.(35.#8.R11.)(34.$28.(36.Vs1,)(34.$28.(36.Vs0,)(34.$28.(36.Vra,)(2:.$28.))))))(2:.(>.$4.(26.$28.))))(2:.(>.$4.(26.$28.))))P,(3.$4.(38.VdB,)R18.)P,(1.=R19.)P,(3.$4.R1:.(39.VdB,))P,Pm2,P,(21.&40.)(22.(21.&8.))Pmo2,$23.Ph2,(24.$25.VL,VHI,)PLB2,(26.$27.)PdW2,$1<.Pyra,(21.&40.)Py0,(21.&40.)Py1,(21.&40.)Py2,(21.&40.)Pya1,(21.&40.)Pya2,(21.&40.)Pya3,(21.&40.)Pya4,(21.&40.)Pya5,(21.&40.)Pya6,(21.&40.)Pya7,(21.&40.)Py3,(21.&40.)Py4,(21.&40.)Py5,(21.&40.)Py6,(21.&40.)P,(29.$25.VL,VHI,Vh,VLB,Vmo,Vm,(9.&40.Vsp,)Vlo,(8.(9.&40.Vsp,)-20.)VdR,$20.R14.R13.R12.R11.(2:.$1<.)R10.(2:.$27.)(34.(>.$4.(26.$28.))(?.$4.(26.$28.)(8.(9.&40.Vsp,)-20.)(34.$28.(35.#8.R29.)(34.$28.(36.Vs1,)(34.$28.(36.Vs0,)(34.$28.(36.Vra,)(2:.$28.))))))(2:.(>.$4.(26.$28.))))(2:.(>.$4.(26.$28.))))P,(1.(38.R2;.)=)P,(3.$4.(38.R12.)(8.(38.R2<.)R31.))(3:.$25.R16.(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.R12.(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,R11.R10.R?.(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))(3?.&40.=)R>.R=.R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(3?.&40.+209<4.)Vfc,(40.(21.&40.))R17.(41.$25.)))(3:.$25.R1:.(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.R15.(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,R14.R13.R12.(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))R11.R10.R?.R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(3?.&40.+209<4.)Vfc,(40.(21.&40.))R1;.(41.$25.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros CS_ VBE VB0 VBA K.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_parts _ _ _ _ _ _ CS_)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros FLt5 NSW EA WR LW CRW CRWL HFW ASW WA8. flat constr:(FLt5) 2%nat. flclear FLt5. intros FLt6 SGW. flat constr:(FLt6) 6%nat. flclear FLt6. intros CW ALW POSW HLW HNW HOW.
    unfold mpi_cells in CW. unfold MPI_MAX_LIMBS in HNW. rewrite EA in CW.
    pose proof (rw_cells_bound _ _ _ _ CW) as WB16. cbn [cells_size csize Nat.add] in WB16.
    pose proof (mpd_abs_lval dW HLW) as AWL.
    (* [comment removed for export] *)
    zstep. rewrite (zx16_small (md_n dW)) by lia.
    zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
    { (* [comment removed for export] *)
      rewrite K0 in HLW. assert (Z0 : mpd_val dW = 0) by (unfold mpd_val; destruct (md_limbs dW); [cbn; clear; lia| cbn in HLW; clear - HLW; lia]).
      eapply (L_loopB vb 1); [exact CS_| exact VBE| exact VB0| exact VBA| rewrite Z0; clear - VB0; lia]. }
    (* [comment removed for export] *)
    assert (HXR : bytes_at psegs mq (md_p dW) (u32s (md_limbs dW)) /\ (0 < md_p dW /\ md_p dW mod 4 = 0)).
    { destruct (md_own dW); [(flat constr:(HOW) 2%nat; flclear HOW; intros _ N0); exfalso; clear - N0 K0; lia| | exfalso; exact (NSW eq_refl)].
      flat constr:(HOW) 4%nat. flclear HOW. intros _ _ P16 U. split; [apply u32arr_ro; exact U|]. flat constr:((HFW eq_refl)) 2%nat. intros P0 _. split; [exact P0| clear - P16; apply Z.mod_divide in P16; [| lia]; apply Z.mod_divide; [lia|]; (flat constr:(P16) 2%nat; flclear P16; intros q Hq); exists (4 * q); lia]. }
    flat constr:(HXR) 2%nat. flclear HXR. intros HXR PR4.
    zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep.
    eapply (L_scanR mq moq (md_p dW) (md_n dW) (md_limbs dW)) with (k := Z.to_nat (md_n dW)) (r := md_n dW).
    all: lazymatch goal with
         | |- MOK _ => exact MK
         | |- bytes_at _ _ _ _ => exact HXR
         | |- Z.of_nat (length _) = _ => exact HLW
         | |- 0 <= md_n _ <= _ => clear - HNW; lia
         | |- _ \/ _ => exact (or_intror PR4)
         | |- Z.to_nat _ = Z.to_nat _ => reflexivity
         | |- 1 <= md_n _ <= md_n _ => clear - HNW K0; lia
         | |- lval _ _ = lval _ _ => reflexivity
         | |- _ = Z_to_bv 64 _ => f_equal; clear; lia
         | |- _ => idtac
         end.
    { (* [comment removed for export] *)
      intros Z0. intros. assert (V0 : mpd_val dW = 0) by (unfold mpd_val; fold (mpd_abs dW); rewrite AWL, Z0; clear; lia).
      eapply (L_loopB vb 1); [exact CS_| exact VBE| exact VB0| exact VBA| rewrite V0; clear - VB0; lia]. }
    (* [comment removed for export] *)
    intros r Hr NZ. intros.
    assert (AP : 0 < mpd_abs dW).
    { rewrite AWL. pose proof (lval_top_nonzero (md_limbs dW) r ltac:(lia) NZ). pose proof (pow32_pos (r - 1) ltac:(lia)).
      pose proof (lval_split (md_limbs dW) r (md_n dW) ltac:(lia)). pose proof (lval_range (skipn (Z.to_nat r) (md_limbs dW)) (md_n dW - r) ltac:(lia)).
      unfold lseg in *. pose proof (pow32_pos r ltac:(lia)). nia. }
    zstep; if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; clear - K1 Hr; lia|].
    zstep. rewrite (sx16_sign _ SGW).
    zstep; if_cases K2; zify_cond K2; rewrite ?signed_lit_small in K2 by (clear - SGW; lia).
    - (* [comment removed for export] *)
      assert (SN : md_sg dW = -1) by (clear - SGW K2; lia).
      assert (VN : mpd_val dW = - mpd_abs dW) by (unfold mpd_val, mpd_abs; rewrite SN; clear; lia).
      zstep. zstep. zstep. zstep. zstep.
      flat constr:((ext_facts _ _ _ _ _ _ dB CS_ opndB)) 6%nat. intros MB CRB_ CRBL_ LOB HFB ASB.
      flat constr:((mc_opnd_sep_we _ _ _ _ _ _ _ _ _ dB CS_ opndB)) 2%nat. intros SEPWB OPSWB.
      flat constr:((mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros SEPWW OPSWW.
      flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros MW _.
      pose proof (HAS 1 (or_introl eq_refl)) as SPA_.
      eapply aevtM_cut.
      { eapply SPA_ with (dX := dW) (dA := dW) (dB := dB) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
        all: try (rewrite ?EA; reflexivity). }
      clear SPA_. cbv beta. intros ms2 mo' PO. unfold mpi_binop_post in PO.
      flat constr:(PO) 31%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 LB2 dW2 r2 E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR.
      injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
      replace (ret_pc (Z_to_bv 64 0x209c0)) with (Z_to_bv 64 0x209c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      flat constr:(RR) 2%nat. flclear RR. intros R1 FLt7. flat constr:(FLt7) 4%nat. flclear FLt7. intros KA KP KF KN.
      assert (CS2 : CST m2 mo2 h2 LB2 [] dW2 [] (FRM j8) []).
      { eapply mc_binop_w; [exact CS_| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact KF| exact KP| exact KN]. }
      assert (Hr2 : (r2 = 0 /\ mpd_val dW2 = mpd_val dW + mpd_val dB) \/ r2 = MBEDTLS_ERR_MPI_ALLOC_FAILED).
      { destruct R1 as [[Hr0 HV]|HrF]; [left; split; [exact Hr0| rewrite HV; clear; lia]| right; exact HrF]. }
      clear MW MB CRB_ CRBL_ LOB HFB SEPWB OPSWB SEPWW OPSWW R1 KF KP MA2 OUT2 PX2 HH HTc MF SOK MI ST CH MK CW HXR.
      flat constr:((cs_parts _ _ _ _ _ _ CS2)) 8%nat. intros HH HTc MF SOK MI ST CH MK.
      zstep; if_cases K3; zify_cond K3.
      + eapply L_epi; [exact CS2| destruct Hr2 as [[Hx _]|Hx]; subst r2; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia|].
        intros ->. exfalso. destruct Hr2 as [[_ _]|Hx]; [apply K3; reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hx; clear - Hx; lia].
      + destruct Hr2 as [[-> HV]|Hx]; [| exfalso; subst r2; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K3; clear - K3; lia].
        eapply K; [exact CS2| rewrite VN; clear - AP; lia| rewrite HV, VBE; reflexivity].
    - (* [comment removed for export] *)
      assert (SP1 : md_sg dW = 1) by (clear - SGW K2; lia).
      zstep. eapply (L_loopB vb (Z.to_nat (mpd_abs dW + 1))); [exact CS_| exact VBE| exact VB0| exact VBA|].
      unfold mpd_val. rewrite SP1, Z.mul_1_l. fold (mpd_abs dW). rewrite Z2Nat.id by (clear - AP; lia). clear - AP VB0. nia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308579027.400000=S2vb2dW2VR2H0". (* [comment removed for export] *)
  Lemma L_loopA : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pvb,$4.PD,$42.Pmq,P,(21.&40.)(22.(21.&8.))Pmoq,$23.Phq,(24.$25.VL,VHI,)PLBq,(26.$27.)PdW,$1<.Pj8,(26.(21.&8.))Pxra,(21.&40.)Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Pa0,(21.&40.)Pa1,(21.&40.)Pa2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)P,(29.$25.VL,VHI,Vh,VLB,Vmo,Vm,(9.&40.Vsp,)Vlo,(8.(9.&40.Vsp,)-20.)VdR,$20.R16.R15.R14.R13.(2:.$1<.)R12.(2:.$27.)(34.(>.$4.(26.$28.))(?.$4.(26.$28.)(8.(9.&40.Vsp,)-20.)(34.$28.(35.#8.R11.)(34.$28.(36.Vs1,)(34.$28.(36.Vs0,)(34.$28.(36.Vra,)(2:.$28.))))))(2:.(>.$4.(26.$28.))))(2:.(>.$4.(26.$28.))))P,(3.$4.(38.VdB,)R19.)P,(1.=R1:.)P,(3.$4.R1;.(39.VdB,))P,(1.(37.(38.R16.))(11.(43.R1;.)R1<.))(3:.$25.R1:.(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.R15.(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,R14.R13.R12.(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))R11.R10.R?.R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(3?.&40.+209<4.)Vfc,(40.(21.&40.))R1;.(41.$25.)))")
(* [comment removed for export] *).
  Proof.
    intros vb D. induction D as [|D IH]; intros until t6; intros CS_ VBE VB0 VBA VR.
    - eapply L_loopA_step; [exact CS_| exact VBE| exact VB0| exact VBA|]. intros. exfalso. clear - VR H0. lia.
    - eapply L_loopA_step; [exact CS_| exact VBE| exact VB0| exact VBA|]. intros until y6. intros CS2 NEG HV.
      eapply IH; [exact CS2| exact VBE| exact VB0| exact VBA| rewrite HV; clear - VR NEG VB0; nia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma opnd_facts0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pmq,P,(21.&40.)(22.(21.&8.))Pmoq,$23.Phq,(24.$25.VL,VHI,)PLBq,(26.$27.)PCS,(26.(>.$4.(26.$28.)))Pd,$1<.P,(29.$25.VL,VHI,Vh,VLB,Vmo,Vm,(9.&40.Vsp,)Vlo,(8.(9.&40.Vsp,)-20.)VdR,$20.R6.R5.R4.R3.(2:.$1<.)VdR,(2:.$27.)R2.(2:.(>.$4.(26.$28.))))P,(6.(=.$1<.R2.$20.)(3.$1<.R2.VdR,))(0.(33.$25.R8.R5.R3.)(0.(1=.VL,R5.Vlo,(2.R3.)+10.)(0.P,(3.$:.(;.R3.)$<.)(1=.VL,R6.Vlo,(10.R4.)(11.+4.(12.R4.)))(0.P,(1>.(3.$:.(;.R3.)$1?.))(6.(7.(8.(10.R4.)(11.+4.(12.R4.)))Vlo,)(7.(8.(9.&40.Vsp,)-20.)(10.R4.)))(0.P,(3.$:.(;.R3.)$<.)(0.(1.=(10.R4.))(7.+1.(12.R4.)))(6.(7.(8.(2.R3.)+10.)Vlo,)(7.(9.&40.Vsp,)(2.R3.))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq CS d CS_ [IN|E]; [exact (ext_facts _ _ _ _ _ _ d CS_ IN)|].
    rewrite E. flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW _ _ _ LW CRW CRWL HFW ASW _.
    split; [exact MW|]. split; [exact CRW|]. split; [exact CRWL|]. split; [exact LW|]. split; [| exact ASW]. intros O. flat constr:((HFW O)) 4%nat. intros P0 _ _ N1. auto.
  Qed.
  Lemma opnd_sep_w0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pmq,P,(21.&40.)(22.(21.&8.))Pmoq,$23.Phq,(24.$25.VL,VHI,)PLBq,(26.$27.)PCS,(26.(>.$4.(26.$28.)))Pd,$1<.P,(29.$25.VL,VHI,Vh,VLB,Vmo,Vm,(9.&40.Vsp,)Vlo,(8.(9.&40.Vsp,)-20.)VdR,$20.R6.R5.R4.R3.(2:.$1<.)VdR,(2:.$27.)R2.(2:.(>.$4.(26.$28.))))P,(6.(=.$1<.R2.$20.)(3.$1<.R2.VdR,))(0.(48.VdR,R3.)(49.VdR,R3.Vlo,(8.(9.&40.Vsp,)-20.)))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq CS d CS_ [IN|E]; [exact (mc_opnd_sep_we _ _ _ _ _ _ _ _ _ d CS_ IN)|].
    rewrite E. exact (mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS_).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L15213097033.1  L1636212821.15  L28621134222.15 L29010565666.132L30875761168.156L41362870958.2  L45290767137.15 L59310678515.3  L66151410442.3  L7190718996.156 L7192832770.127 00000400O00\00]00d00l01M01X01a02A02aS2dBS1L2HI2sp1h4HTOP2hq3SPB3HTcS1L2sp2lo3SLOFS2sp2dRS3dW22WAS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2dB2Z03HBPS1r2Hr2K0S1L3HLS2sp2dR2lo3SLO3ACL3SPB3ACPS1L3HLS2sp2dR2lo3SLO3ACL3SPB3ACP". (* [comment removed for export] *)
  Lemma L_call : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pmq,P,(21.&40.)(22.(21.&8.))Pmoq,$23.Phq,(24.$25.VL,VHI,)PLBq,(26.$27.)Pj8,(26.(21.&8.))Pxra,(21.&40.)Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Pa0,(21.&40.)Pa1,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)P,(29.$25.VL,VHI,Vh,VLB,Vmo,Vm,(9.&40.Vsp,)Vlo,(8.(9.&40.Vsp,)-20.)VdR,$20.R14.R13.R12.R11.(2:.$1<.)VdR,(2:.$27.)(34.(>.$4.(26.$28.))(?.$4.(26.$28.)(8.(9.&40.Vsp,)-20.)(34.$28.(35.#8.R10.)(34.$28.(36.Vs1,)(34.$28.(36.Vs0,)(34.$28.(36.Vra,)(2:.$28.))))))(2:.(>.$4.(26.$28.))))(2:.(>.$4.(26.$28.))))P,(6.(3.$4.(39.VdB,)=)(3.$4.(4:.VdB,)+1.))(3:.$25.R15.(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.R11.(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,R10.R?.R>.(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))R=.R<.(3?.&40.(2.VdA,))R;.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(3?.&40.+20994.)Vfc,(40.(21.&40.))R16.(41.$25.)))")
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
    zstep. zstep. zstep. zstep.
    pose proof HDIV as SPD. unfold mpi_div_mpi_stmt, P_MPI_DIV_MPI in SPD.
    eapply aevtM_cut.
    { eapply SPD with (dX := dR) (dA := dA) (dB := dB) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia). }
    clear SPD. cbv beta. intros ms2 mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 31%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR.
    injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
    replace (ret_pc (Z_to_bv 64 0x209a4)) with (Z_to_bv 64 0x209a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 2%nat. flclear RR. intros (Hr & HBP) FLt8. flat constr:(FLt8) 4%nat. flclear FLt8. intros KA KP KF KN.
    assert (CS2 : CST m2 mo2 h2 LB2 [] dW2 [] (FRM j8) []).
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
      zstep.
      pose proof (mpd_val_abs dW2 SGW2) as WA.
      eapply (L_loopA (mpd_abs dB) (Z.to_nat (mpd_abs dW2 + 1))); [exact CS2| exact VBE| exact HBP| reflexivity|].
      rewrite Z2Nat.id by (clear - WA; lia). clear - WA HBP. nia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Section ScanB0.
    Variables (mq : mem) (moq : Model) (pB nB : Z) (ys : list word).
    Hypothesis MKq : MOK moq.
    Hypothesis HXB : bytes_at psegs mq pB (u32s ys).
    Hypothesis LXB : Z.of_nat (length ys) = nB.
    Hypothesis BNB : 0 <= nB <= 10000.
    Hypothesis PB4 : nB = 0 \/ 0 < pB /\ pB mod 4 = 0.
    Variables (xra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word).
    Hypothesis KZ : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "P,(3.$4.(44.Vys,VnB,)=)Pwa0,(21.&40.)Pwa1,(21.&40.)Pwa3,(21.&40.)(3:.$25.Vmoq,(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.Vxra,(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,Vt0,Vt1,Vt2,(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))R3.R2.(3?.&40.(2.VdA,))R1.Va4,Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(3?.&40.+20994.)Vfc,(40.(21.&40.))Vmq,(41.$25.)))")
(* [comment removed for export] *).
    Hypothesis KNZ : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pr,$4.P,(0.(7.+1.R1.)(7.R1.VnB,))P,(1>.(3.$4.(45.Vys,(46.(47.R2.+1.)))=))Pwa0,(21.&40.)Pwa3,(21.&40.)(3:.$25.Vmoq,(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.Vxra,(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,Vt0,Vt1,Vt2,(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))R2.(3?.&40.R5.)(3?.&40.(2.VdA,))R1.Va4,Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(3?.&40.+20988.)Vfc,(40.(21.&40.))Vmq,(41.$25.)))")
(* [comment removed for export] *).
    Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L11014201954.105L13036769295.105L19168960846.103L1962781522.105 L23917382008.105L23970764156.104L26188898998.105L31326834835.105L40926673579.105L41528776408.97 L41530891349.100L42468637227.102L54425554052.10100000J00g01801`02>02Y02m03J03d06808Y08m09DS2sp2pB2nB2ys1k1r2Hk2Hr2wyS2sp2pB2nB2ys1k1r2Hk2Hr2wy2K2S2sp2pB2ys1k1r2HkS2sp2pB2nB2ys3PB41k1r2Hk2Hr2wy3LYr2K12K2S2sp2pB2nB2ys3PB41k1r2Hk2Hr2wyS2sp2nB2ys3BNB1k1r2Hk2Hr2wyS2sp2pB2ys1k1r2Hk2wyS2sp2pB2nB2ys1k1r2Hk2Hr2wy2K2S2sp2pB2nB2ys1k1r2Hk2Hr2wyS1L2HI2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m2mo1h2LB2dR2dA2dB2lo2mq3moq2pB2nB2ys3xra2t02t12t22a42a52a62a72t32t42t52t61r3wa32Hk2HrS1L2HI2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m2mo1h2LB2dR2dA2dB2lo2mq3moq2pB2nB2ys3LXB3PB43xra2t02t12t22a42a52a62a72t32t42t52t61k1r3wa32Hk2Hr2NYS2sp2pB2ys1k1r2Hk2wyS2sp2pB2nB2ys1k1r2Hk2Hr". (* [comment removed for export] *)
    Lemma L_scanB0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pk,$42.Pr,$4.Pwa0,(21.&40.)Pwa1,(21.&40.)Pwa3,(21.&40.)P,(3.$42.(46.R4.)R5.)P,(0.(7.+1.R5.)(7.R5.VnB,))P,(3.$4.(44.Vys,VnB,)(44.Vys,R6.))P,(3.(21.&40.)R5.(3?.&40.R7.))P,(3.(21.&40.)R7.(3?.&40.(47.(8.VpB,(11.+4.R8.))+4.)))(3:.$25.Vmoq,(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.Vxra,(3?.&40.(8.(9.&40.Vsp,)-20.))Vgp,Vtp,Vt0,Vt1,Vt2,(3?.&40.(2.VdB,))(3?.&40.(2.VdR,))R8.R7.(3?.&40.(2.VdA,))R6.Va4,Va5,Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(3?.&40.+20970.)Vfc,(40.(21.&40.))Vmq,(41.$25.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros r wa0 wa1 wa3 Hk Hr INV -> ->; [lia|].
      destruct (nth_error ys (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; lia].
      pose proof (u32ro_read psegs mq pB ys (r - 1) wy _ HXB NY ltac:(lia) eq_refl) as RDY.
      zstep. clear RDY. pose proof (limb32_of_read ys r wy NY) as LYr.
      pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(lia)) as By.
      zstep; if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
      - assert (NZ : limb32 ys (Z.to_nat (r - 1)) <> 0) by (rewrite LYr; intros E; apply K1; rewrite E; reflexivity).
        apply (KNZ r); [lia| exact NZ].
      - apply (proj1 (sxz_zero_iff _ By)) in K1.
        zstep. zstep. zstep; if_cases K2; zify_cond K2.
        + eapply (IH (r - 1)); [lia| lia| rewrite INV; apply lval_drop_zero; [lia| rewrite LYr; exact K1]| f_equal; lia| f_equal; lia].
        + zstep. apply KZ. rewrite INV, (lval_drop_zero ys r) by (try lia; rewrite LYr; exact K1). replace (r - 1) with 0 by lia. apply lval_0.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End ScanB0.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L1429900444.1   L15281804514.1  L21765854580.93 L21887662552.92 L22706556809.7  L24897143244.3  L27775132660.93 L29010566049.116L33510041944.93 L34290115814.88 L36950928818.2  L40855853891.3  L41417956170.111L43061661626.86 L46933647127.2  L47729596474.3  L50667210948.0  L55155570482.3  L58177949655.111L59308546259.3  L59308628304.4  L59314955108.1  L62502502072.1  L63432243226.108L66083662040.93 L66988371244.110L66990871592.108L66990871850.117L9716869748.92  00000400800<00@00V00Z00^01@01D01H01I01T01`02502=02H02I02R02^02h03403703;03K03O03_03o040044S2spS2spS2spS2spS1L3HLS2sp2lo3SLO1x2HxS2dBS2spS2sp2dB3SPB4POSB3HNB4BB163PB41r2HrS2spS2spSS2dB3HNB2K0S2sp2dB4BB16S1L3HLS2sp2lo3SLO3SPBS2dB3HNBS2dB3SGB2K2SS2dB1q2HqS2sp2dB4BB16S2dB2K02N0S2dB1r2Hr2K1S1ES2dBS2sp2dB3HNB4BB16S2spS2sp2dB3HNB4BB16S2sp2dB3HNB4BB16FS2sp". (* [comment removed for export] *)
  Lemma L_mod : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mod_mpi ()) "Pt0,(21.&40.)Pt1,(21.&40.)Pt2,(21.&40.)Pa3,(21.&40.)Pa4,(21.&40.)Pa5,(21.&40.)Pa6,(21.&40.)Pa7,(21.&40.)Pt3,(21.&40.)Pt4,(21.&40.)Pt5,(21.&40.)Pt6,(21.&40.)(3:.$25.Vmo,(3;.$25.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdR,(3<.VLB,VdR,VdA,VdB,)Vlo,Vm,Vmo,)(3=.(3>.Vra,Vsp,Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(3?.&40.(2.VdR,))(3?.&40.(2.VdA,))(3?.&40.(2.VdB,))R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(3?.&40.+2093<.)Vfc,(40.(21.&40.))Vm,(41.$25.)))")
(* [comment removed for export] *).
  Proof.
    intros.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK.
    pose proof ST0 as ST. pose proof MI0 as MI. pose proof es_at as ESA.
    carve_frame 32%nat ST.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    set (mI := m) in HH0, MR0, MA0, MB0, MI0, SOK0, ST0, ESA.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (j8 := j) in FR end.
    assert (MU1 : munch [(lo, SP)] m m1).
    { eapply munch_weaken; [| exact MU]. intros x Hx. cbn in Hx |- *. clear - Hx SLO HLS. lia. }
    pose proof HH0 as HH0'. pose proof SOK0 as SOK0'. pose proof MI0 as MI0'. pose proof MR0 as MR0'. unfold mI in HH0', SOK0', MI0', MR0', ESA.
    assert (CS1 : CST m1 mo h LB [] dR [] (FRM j8) []).
    { eapply mc_init; [exact HH0'| exact SOK0'| exact MI0'| exact MR0'| exact ESA| exact MU1| exact WM| exact MI| exact ST| constructor| | |].
      - intros i j di dj Hi. destruct i; discriminate Hi.
      - constructor; [exact FR| constructor].
      - constructor; [| constructor]. cbn [fst snd cells_size csize Nat.add]. split; [clear; lia|]. split; [clear; lia| intros d []]. }
    clear FR MU WM MU1 HH0' SOK0' MI0' MR0' ESA.
    flat constr:((cs_parts _ _ _ _ _ _ CS1)) 8%nat. intros HH1 HT1 MF1 SOK1 MI1 ST1 CH1 MK1.
    flat constr:((opnd_facts0 _ _ _ _ _ dB CS1 (or_introl opndB))) 6%nat. intros FLt9 _ _ _ HFB _. flat constr:(FLt9) 2%nat. flclear FLt9. intros FLt10 SGB. flat constr:(FLt10) 6%nat. flclear FLt10. intros CSB ALB POSB HLB HNB HOB. unfold mpi_cells in CSB. unfold MPI_MAX_LIMBS in HNB.
    pose proof (rw_cells_bound _ _ _ _ CSB) as BB16. cbn [cells_size csize Nat.add] in BB16.
    pose proof (mpd_abs_lval dB HLB) as ABB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite (zx16_small (md_n dB)) by lia. zstep.
    zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
    { (* [comment removed for export] *)
      eapply L_call; [exact CS1|]. left. rewrite ABB, K0. apply lval_0. }
    assert (HXB : bytes_at psegs m1 (md_p dB) (u32s (md_limbs dB)) /\ (0 < md_p dB /\ md_p dB mod 4 = 0)).
    { destruct (md_own dB); [(flat constr:(HOB) 2%nat; flclear HOB; intros _ N0); exfalso; clear - N0 K0; lia| |].
      - flat constr:(HOB) 4%nat. flclear HOB. intros _ _ P16 U. split; [apply u32arr_ro; exact U|]. flat constr:((HFB eq_refl)) 2%nat. intros P0 _. split; [exact P0| clear - P16; apply Z.mod_divide in P16; [| lia]; apply Z.mod_divide; [lia|]; (flat constr:(P16) 2%nat; flclear P16; intros q Hq); exists (4 * q); lia].
      - flat constr:(HOB) 5%nat. flclear HOB. intros _ P4 P0 BY _. auto. }
    flat constr:(HXB) 2%nat. flclear HXB. intros HXB PB4.
    zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep.
    eapply (L_scanB0 m1 mo (md_p dB) (md_n dB) (md_limbs dB)) with (k := Z.to_nat (md_n dB)) (r := md_n dB).
    all: lazymatch goal with
         | |- MOK _ => exact MK1
         | |- bytes_at _ _ _ _ => exact HXB
         | |- Z.of_nat (length _) = _ => exact HLB
         | |- 0 <= md_n _ <= _ => clear - HNB; lia
         | |- _ \/ _ => exact (or_intror PB4)
         | |- Z.to_nat _ = Z.to_nat _ => reflexivity
         | |- 1 <= md_n _ <= md_n _ => clear - HNB K0; lia
         | |- lval _ _ = lval _ _ => reflexivity
         | |- _ = Z_to_bv 64 _ => f_equal; clear; lia
         | |- _ => idtac
         end.
    { (* [comment removed for export] *) intros Z0. intros. eapply L_call; [exact CS1|]. left. rewrite ABB. exact Z0. }
    (* [comment removed for export] *)
    intros r Hr NZ. intros.
    zstep; if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; clear - K1 Hr; lia|].
    zstep. rewrite (sx16_sign _ SGB).
    zstep; if_cases K2; zify_cond K2; rewrite ?signed_lit_small in K2 by (clear - SGB; lia).
    - (* [comment removed for export] *)
      zstep. eapply L_epi; [exact CS1| clear; lia| intros E; exfalso; clear - E; lia].
    - eapply L_call; [exact CS1|]. right. clear - SGB K2. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Walk.

  Theorem P_mpi_mod_mpi_ok : mpi_mod_mpi_stmt psegs L HI P_MPI_MOD_MPI' MSF.
  Proof.
    unfold mpi_mod_mpi_stmt, mpi_binop_stmt_nb, P_MPI_MOD_MPI'. intros until lo.
    intros HH MX MA MB SXA SXB SAB NSX NEB OPA OPB CRA CRAL CRB CRBL WRX XLO ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    eapply L_mod; eassumption.
  Qed.
End ModP.

