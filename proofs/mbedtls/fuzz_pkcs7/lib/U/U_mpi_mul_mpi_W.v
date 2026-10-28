(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney MpiJourney2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_core_mul U_mpi_add_abs_W U_mpi_add_abs_C U_mpi_mul_stmt U_mpi_mul_int_W U_mpi_mul_int U_mpi_lset.
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
Ltac2 gd_tbl_P_mpi_mul_mpi_W () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.XJ"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.BJ"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.JB"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Corelib.Init.Datatypes.nat"].


Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L61055709130.0L62756896884.2000001006SS1a1b". (* [comment removed for export] *)
Lemma sign_mulmod16 : forall a b, (b mod 2^64 * (a mod 2^64)) mod 2^16 = (a * b) mod 2^16.
Proof.
  intros a b. rewrite <- (Z.mod_mod_divide (b mod 2^64 * (a mod 2^64)) (2^64) (2^16)) by (exists (2^48); reflexivity).
  rewrite <- Z.mul_mod by (clear; lia). rewrite (Z.mod_mod_divide) by (exists (2^48); reflexivity). f_equal. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Section W.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Variables (ra sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m1 : mem) (mo1 : Model) (h1 : HST usegs L HI) (LB1 : list blk) (lo : Z) (MSF : Z) (FRL : list cell)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own)
            (Aa sA nA pA : Z) (ys : list word) (padA : word) (ownA : limb_own)
            (Ba sB nB pB : Z) (zs : list word) (padB : word) (ownB : limb_own)
            (POST : config -> Prop).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Local Notation dA := (mkMPD Aa sA nA pA ys padA ownA).
  Local Notation dB := (mkMPD Ba sB nB pB zs padB ownB).
  Local Notation SPJ := (Z_to_bv 64 (bv_unsigned sp - 112)).
  Hypothesis MSFE : MSF = U_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 304 - hl_stack L.
  Hypothesis ACL0 : alloc_ceiling <= lo.
  Hypothesis FRSZ : Z.of_nat (cells_size FRL) = 112%Z.
  Hypothesis JCX : JC usegs L HI h1 LB1 m1 mo1 dX SPJ lo 0 [].
  Hypothesis XS0 : X + 16 <= lo \/ bv_unsigned sp <= X.
  Hypothesis JBA : JB usegs L LB1 m1 dX SPJ lo dA.
  Hypothesis JBB : JB usegs L LB1 m1 dX SPJ lo dB.
  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ usegs L HI h1 LB1 m1 mo1 dX SPJ lo 0 [] []).
  Local Notation XJ1 An cnt := (XJ usegs L HI h1 LB1 m1 mo1 dX SPJ lo 0 [] [(An, 4 * cnt)]).
  Local Notation BJE dE := (BJ usegs SPJ dE).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1 NM1]; cbn [app] in HH1.
  Local Ltac zb_split K := repeat match type of K with
    | context [Z.b2z (?x <? ?y)] => revert K; destruct (Z.ltb_spec x y); cbn [Z.b2z]; intro K
    | context [Z.b2z (?x <=? ?y)] => revert K; destruct (Z.leb_spec x y); cbn [Z.b2z]; intro K
    | context [Z.b2z (?x =? ?y)] => revert K; destruct (Z.eqb_spec x y); cbn [Z.b2z]; intro K
    end.
  Local Ltac clear_dm := repeat match goal with
    | H : context [Z.div _ _] |- _ => clear H
    | H : context [Z.modulo _ _] |- _ => clear H
    end.
  Local Ltac chk_core K :=
    zify_cond K; rewrite ?land_3_mod', ?land_7_mod' in K; rewrite ?unsigned_lit, ?signed_lit_small in K by lia;
    rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2, ?land_3_mod', ?land_7_mod' in K by lia; zb_split K;
    rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in K; rewrite ?unsigned_lit in K by lia;
    first [ lia | rewrite ?unsigned_lit_wrap in K; lia ].
  Local Ltac chk := let K := fresh "K" in if_cases K;
    [ exfalso; first [ revert K; clear_dm; intro K; chk_core K | chk_core K ]
    | clear K ].
  Local Ltac zeq := apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; clear; Z.div_mod_to_equations; lia.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L1349803706.7200000PS1L2sp2lo3FRL4SLO23HLS3ACL3SPB1H". (* [comment removed for export] *)
  Lemma SPJU : bv_unsigned SPJ = bv_unsigned sp - 112.
  Proof. jc_open. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos. apply unsigned_lit. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition KCL_stmt : Prop :=
    forall (t0 t1 t2 raj x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x22 x23 x24 t3 t4 t5 t6 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd) (r pc : Z),
    XJ0 hc LBc mc moc dXc -> BJE dA LBc mc dXc -> BJE dB LBc mc dXc -> rw_cells usegs mc (bv_unsigned sp - 112) FRL ->
    (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) -> (pc = 0x20d44 \/ pc = 0x20d20 \/ pc = 0x20de4) ->
    aevtM usegs moc POST (MS (mkR raj SPJ gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 r) x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Hypothesis KCL : KCL_stmt.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L22961730820.62000008S2sp3FRL". (* [comment removed for export] *)
  Lemma fr_presx : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "PLBp,(3.$4.)PXI,(3.$1:.)Pmc,P,(0.&40.)(5.(0.&8.))Pmc',P,(0.&40.)(5.(0.&8.))P,(1;.$2.VL,R4.(<.(=.&40.Vsp,)+70.)R3.R2.R1.)P,(11.$2.R3.(<.(=.&40.Vsp,)+70.)VFRL,)P,(1<.R5.(<.(=.&40.Vsp,)+70.)+70.)(11.$2.R4.(<.(=.&40.Vsp,)+70.)VFRL,)")
(* [comment removed for export] *).
  Proof.
    intros LBp XI mc mc' HP FR D. eapply heap_presx_rw_cells; [exact HP| exact FR| rewrite FRSZ; apply client_range_stack; lia| rewrite FRSZ; exact D].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L10257851201.7 L21516146488.2 L25721051894.2 L39280637297.0 L40362700714.0 L4112444482.2  L41149646033.11L4769765241.0  L49965254466.5 L49965663300.6 L53134281077.4 L5506491570.2  L59308587280.2 L59308664813.4 L6721511659.7  L8111968256.10 00000I00O00U00V00W00_01C01D01T01i02802@02F02U02n03DS2nE2pE2ws4LENE3NE13PE01KS1p2P0S1k2HKSSS2nE3NE1S1L2sp2lo4SLO22pE1n1p3HLS3ACL2PC3ESPSS1L2nE2pE3ACV2R3S1L4IMGC2nE2pE3ACV2I1S1L2lo4ACL03ACPS2nE3NE1S1q2HqS2nE2ws4LENE2ENS2nE2pE2ws4LENE3NE13PE01KS1L2nE2pE1n1p2PI2I02I1". (* [comment removed for export] *)
  Lemma rider_facts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "PEa,$8.PsE,$8.PnE,$8.PpE,$8.Pws,(3.(0.&40.))PpadE,(0.&40.)PownE,$1=.Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.Psg,$8.Pn,$8.Pp,$8.Pxs,(3.(0.&40.))Pk,$8.P,(1>.$2.VL,VLB1,Vm1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,(:.R10.R?.R>.R=.R<.R;.R:.))P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R:.R9.R8.R7.(:.VX,R6.R5.R4.R3.VpadX,$1?.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.R12.R11.R10.R?.R>.R=.R<.)R:.R9.(:.VX,R7.R6.R5.R4.VpadX,$1?.))P,(20.(21.=R4.)(21.R4.R11.))(20.(22.$2.R;.R11.(23.R10.))(20.(13.$8.(24.(25.(0.&40.)R10.))R12.)(20.(13.$8.(26.R11.+4.)=)(20.(12.(13.$8.R5.=)(27.=R11.))(20.(12.(21.(28.R11.(29.+4.R12.))R7.)(21.(28.R7.(29.+4.R8.))R11.))(20.(27.(28.R11.(29.+4.R12.))(2:.+2.+40.))(20.(12.(21.(28.R11.(29.+4.R12.))Vlo,)(21.(<.(=.&40.Vsp,)+70.)R11.))(20.(11.$2.R;.R14.(2;.$?.(2<.(;.&40.R11.))(2;.$?.(2=.(;.&40.R13.))(2;.$?.(2=.(;.&40.R12.))(2;.$?.(2>.R?.)(>.$?.))))))(20.(12.(13.$8.R13.+1.)(13.$8.R13.-1.))(20.(20.(21.=R12.)(21.R12.+2710.))(20.(27.=R14.)(20.(21.(28.R14.+10.)(2:.+2.+40.))(13.$8.(26.R14.+8.)=)))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until k. intros JBE J BE HK. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU as SPJU.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ N1 XIN XPAL ARR1 P0 PC PI.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBE _ _ _ BE)) 8%nat. intros E0 E16 EAL LENE NRE ES OWNE0 OWNE1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BE))) 2%nat. intros FLt1 SGE. flat constr:(FLt1) 6%nat. flclear FLt1. intros CE _ _ _ _ OWE. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CE, SGE, OWE. unfold mpi_cells in CE.
    pose proof BE as [_ ESS ESL]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ESS, ESL.
    destruct ownE.
    - flat constr:((OWNE0 eq_refl)) 2%nat. intros EP EN. subst pE. assert (ws = []) as -> by (destruct ws; [reflexivity| exfalso; cbn [length] in LENE; clear - LENE EN; lia]).
      clear LENE. subst nE.
      split; [unfold bytes_at; rewrite u32s_length; cbn [length Nat.mul]; split; [clear; lia|]; split; [clear; lia|]; intros q Hq; exfalso; clear - Hq; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [left; clear - HK; lia|]. split; [left; clear - P0; lia|]. split; [clear; lia|]. split; [left; clear - ACL0 ACP; lia|].
      split; [exact CE|]. split; [exact SGE|]. split; [exact NRE|]. split; [exact E0|]. split; [exact E16| exact EAL].
    - flat constr:((OWNE1 ltac:(discriminate))) 6%nat. intros NE1 PE0 PE4 EBY ELS EIN. flat constr:((EIN eq_refl)) 2%nat. intros EIN1 _.
      flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _. flat constr:((proj1 (Forall_forall _ _) HBR0 _ EIN1)) 5%nat. intros _ _ _ R3 _. cbn in R3.
      split; [exact EBY|]. split; [exact LENE|]. split; [exact PE4|]. split; [right; exact PE0|].
      split; [destruct (ESL eq_refl ltac:(discriminate)) as [D|D]; [right; exact D| left; exact D]|]. split; [clear - R3 ACV; lia|]. split; [exact ELS|].
      split; [exact CE|]. split; [exact SGE|]. split; [exact NRE|]. split; [exact E0|]. split; [exact E16| exact EAL].
    - flat constr:((OWNE1 ltac:(discriminate))) 6%nat. intros NE1 PE0 PE4 EBY ELS _. destruct OWE as (_ & _ & _ & _ & [ERO|[ESP E64]]).
      2: { (* [comment removed for export] *) rewrite ?SPJU in ESP.
           split; [exact EBY|]. split; [exact LENE|]. split; [exact PE4|]. split; [right; exact PE0|].
           split; [right; clear - ESP PC ACL SLO2 HLS; lia|]. split; [exact E64|]. split; [exact ELS|].
           split; [exact CE|]. split; [exact SGE|]. split; [exact NRE|]. split; [exact E0|]. split; [exact E16| exact EAL]. }
      pose proof (ERO 0 ltac:(clear - NE1; lia)) as RO0. rewrite Z.add_0_r in RO0.
      pose proof (bytes_at_bound _ _ _ _ EBY) as K. rewrite u32s_length in K.
      pose proof (ROIMG pE RO0 ltac:(clear - K PE0 LENE NE1; lia)) as I0.
      pose proof (ERO (4 * nE - 1) ltac:(clear - NE1; lia)) as RO1. pose proof (ROIMG (pE + (4 * nE - 1)) RO1 ltac:(clear - K PE0 NE1 LENE; lia)) as I1.
      split; [exact EBY|]. split; [exact LENE|]. split; [exact PE4|]. split; [right; exact PE0|].
      split; [clear - I0 I1 PI N1 NE1; lia|]. split; [clear - I1 IMGC ACV; lia|]. split; [exact ELS|].
      split; [exact CE|]. split; [exact SGE|]. split; [exact NRE|]. split; [exact E0|]. split; [exact E16| exact EAL].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_TAIL : forall (i j : Z) (t0 t1 t2 raj a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 t3 t4 t5 t6 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (sg n p : Z) (xs : list word),
    XJ0 hc LBc mc moc (mkMPD X sg n p xs padX LHeap) ->
    BJE dA LBc mc (mkMPD X sg n p xs padX LHeap) -> BJE dB LBc mc (mkMPD X sg n p xs padX LHeap) ->
    rw_cells usegs mc (bv_unsigned sp - 112) FRL ->
    0 <= i <= nA -> 0 <= j <= nB -> i + j <= n ->
    aevtM usegs moc POST (MS (mkR raj SPJ gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 Ba) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 Aa) (Z_to_bv 64 i) x20 x21 x22 x23 (Z_to_bv 64 (- j)) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20dac) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until xs. intros J BA BB FRc HI_ HJ HN. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU as SPJU. rewrite ?SPJU in *.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ N1 XIN XPAL ARR1 P0 PC PI.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof JBA as [MA0 OA CRA CRAL SXA]. flat constr:(OA) 5%nat. intros OA1 OA2 OA3 OA4 OA5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    pose proof JBB as [MB0 OB CRB CRBL SXB]. flat constr:(OB) 5%nat. intros OB1 OB2 OB3 OB4 OB5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ BA)) 8%nat. intros A0 A16 AAL LENA NRA AS OWNA0 OWNA1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ BB)) 8%nat. intros B0 B16 BAL LENB NRB BS OWNB0 OWNB1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BA))) 2%nat. intros (CEA & _) SGA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEA, SGA. unfold mpi_cells in CEA.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BB))) 2%nat. intros (CEB & _) SGB. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEB, SGB. unfold mpi_cells in CEB.
    pose proof BA as [_ ASS ASL]. pose proof BB as [_ BSS BSL]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ASS, ASL, BSS, BSL.
    clear HH1 SOK1 HPX1 FR1.
    specialize (ASS eq_refl). specialize (BSS eq_refl). pose proof (XP1 eq_refl) as XP. rewrite Z.sub_0_r in ST1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    flat constr:((rider_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i JBA J BA HI_)) 9%nat. intros ABY LENA' PA4 PAZ ASEP A64 ALS CEA3 _.
    flat constr:((rider_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j JBB J BB HJ)) 9%nat. intros BBY LENB' PB4 PBZ BSEP B64 BLS CEB3 _.
    do 5 zstep.
    lazymatch goal with |- context [Z_to_bv 64 (0 - ?e)] => replace (Z_to_bv 64 (0 - e)) with (Z_to_bv 64 j) by zeq end.
    zstep.
    pose proof U_mpi_core_mul_spec as SPc. unfold mpi_core_mul_stmt, U_MPI_CORE_MUL, MPI_CORE_MUL_STACK in SPc.
    eapply aevtM_cut_evt; [exact MK1| eapply SPc with (xs := xs) (ys := ys) (zs := zs) (an := i) (bn := j) (X := p) (A := pA) (B := pB) (lo := lo);
      rewrite ?SPJU; try reflexivity; try eassumption|].
    - clear - HI_; lia. - clear - HJ; lia. - clear - HN NR1; lia. - clear - HN LEN1; lia. - rewrite LENA'; clear - HI_; lia. - rewrite LENB'; clear - HJ; lia.
    - rewrite LENA', LEN1. exact ASEP. - rewrite LENB', LEN1. exact BSEP.
    - clear - XPAL. Z.div_mod_to_equations. lia. - rewrite LEN1. clear - PC ACV; lia. - rewrite LENA'. exact A64. - rewrite LENB'. exact B64.
    - clear - SLO2 HLS; lia. - clear - SPA. Z.div_mod_to_equations. lia.
    - left. rewrite LEN1. clear - PC ACL0. lia. - rewrite LENA'. exact ALS. - rewrite LENB'. exact BLS.
    - cbv beta. intros ms' PO. unfold mpi_core_mul_post in PO.
      flat constr:(PO) 25%nat. flclear PO. intros z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 m4 xs' -> MU4 WM4 MI4 ARR4 LEN4 SK4 ST4.
      unfold MPI_CORE_MUL_STACK in MU4. rewrite ?SPJU in MU4, ST4.
      replace (ret_pc (Z_to_bv 64 0x20dc4)) with (Z_to_bv 64 0x20dc4) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J MU4 WM4 MI4 ltac:(rewrite SPJU, Z.sub_0_r; exact ST4)
                    ltac:(intros a NO; destruct (outside_dec [(p, p + 4 * (i + j)); (bv_unsigned sp - 112 - 176, bv_unsigned sp - 112)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; rewrite ?SPJU; clear - O HN HI_ HJ SLO2 HLS; lia])
                    ltac:(cbn; rewrite ?SPJU; clear - PC ACL0 SLO2 HLS HN HI_ HJ; lia) ltac:(cbn; rewrite ?SPJU; clear - XP XS0 HN HI_ HJ SLO2 HLS; lia) ARR4
                    ltac:(rewrite LEN4; reflexivity)) as J4.
      pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA MU4 WM4 ltac:(cbn; rewrite ?SPJU; clear - ASS AS HN HI_ HJ SLO2 HLS; lia) ltac:(intros AN; cbn; rewrite ?SPJU; pose proof (ASL eq_refl AN); pose proof (OA5 AN); clear - H H0 HN HI_ HJ SLO2 HLS; lia)) as BA4.
      pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB MU4 WM4 ltac:(cbn; rewrite ?SPJU; clear - BSS BS HN HI_ HJ SLO2 HLS; lia) ltac:(intros BN; cbn; rewrite ?SPJU; pose proof (BSL eq_refl BN); pose proof (OB5 BN); clear - H H0 HN HI_ HJ SLO2 HLS; lia)) as BB4.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BA4, BB4.
      assert (BA4' : BJE dA LBc m4 (mkMPD X sg n p xs' padX LHeap)) by (destruct BA4 as [k1 k2 k3]; constructor; assumption).
      assert (BB4' : BJE dB LBc m4 (mkMPD X sg n p xs' padX LHeap)) by (destruct BB4 as [k1 k2 k3]; constructor; assumption).
      clear BA4 BB4. rename BA4' into BA4. rename BB4' into BB4.
      assert (FR4 : rw_cells usegs m4 (bv_unsigned sp - 112) FRL).
      { eapply rw_cells_transport; [exact FRc| exact MU4| exact WM4|]. cbn. rewrite FRSZ. clear - PC ACL0 SLO2 HLS HN HI_ HJ. lia. }
      assert (CX4 : rw_cells usegs m4 X [C8 (Z_to_bv 64 p); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 padX]).
      { eapply rw_cells_transport; [exact CX1| exact MU4| exact WM4|]. cbn. rewrite ?SPJU. clear - XP XS0 HN HI_ HJ SLO2 HLS. lia. }
      assert (CEA4 : rw_cells usegs m4 Aa [C8 (Z_to_bv 64 pA); C2 (Z_to_bv 64 sA); C2 (Z_to_bv 64 nA); C4 padA]).
      { eapply rw_cells_transport; [exact CEA3| exact MU4| exact WM4|]. cbn. clear - ASS AS HN HI_ HJ SLO2 HLS. lia. }
      assert (CEB4 : rw_cells usegs m4 Ba [C8 (Z_to_bv 64 pB); C2 (Z_to_bv 64 sB); C2 (Z_to_bv 64 nB); C4 padB]).
      { eapply rw_cells_transport; [exact CEB3| exact MU4| exact WM4|]. cbn. clear - BSS BS HN HI_ HJ SLO2 HLS. lia. }
      clear MU WM J JX BA BB MI1 ST1 CX1 CEA3 CEB3 ARR1 FRc SPc MU4 WM4 SK4.
      clear ASEP BSEP A64 B64 ALS BLS PAZ PBZ ABY BBY PA4 PB4 AS BS PI XIN OA2 OA3 OA4 OA5 OB2 OB3 OB4 OB5 CRA CRAL CRB CRBL.
      pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl usegs m4) as WM.
      zstep. if_cases K9; zify_cond K9.
      + zstep. rewrite sx16_small by (clear - SGA; lia). zstep. rewrite sx16_small by (clear - SGB; lia). zstep.
        replace (Z_to_bv 64 (sB mod 18446744073709551616 * (sA mod 18446744073709551616))) with (Z_to_bv 64 (sA * sB))
          by (apply Z_to_bv_eqm; change 18446744073709551616 with (2 ^ 64); rewrite <- (Z.mul_mod sB sA (2 ^ 64)) by (clear; lia); f_equal; clear; lia).
        assert (SP1 : sA * sB = 1 \/ sA * sB = -1) by (clear - SGA SGB; destruct SGA as [-> | ->]; destruct SGB as [-> | ->]; cbn; tauto).
        remember (sA * sB) as sg' eqn:ESG. clear ESG.
        destruct SP1 as [EP|EP]; rewrite EP.
        all: clear MU WM CEA4 CEB4; pose proof (munch_refl [(X, X + 16)] m4) as MU; pose proof (wmono_refl usegs m4) as WM.
        all: zstep; zstep.
        all: match goal with MI5 : mem_inv usegs ?mm, CX5 : rw_cells usegs ?mm X _ |- aevtM _ _ _ (MS _ _ _ _ _ ?mm _) =>
          first [ pose proof (xj_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ 1 J4 MU WM MI5 CX5 ltac:(left; reflexivity)) as J5
                | pose proof (xj_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ (-1) J4 MU WM MI5 CX5 ltac:(right; reflexivity)) as J5 ] end.
        all: cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
        all: eapply KCL; [exact J5| | | | left; reflexivity| right; right; reflexivity].
        all: try match goal with FR5 : rw_cells usegs _ (bv_unsigned sp - 112) FRL |- _ => exact FR5 end.
        all: try (pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA4 MU WM ltac:(cbn; clear - SXA; lia) ltac:(intros AN; cbn; pose proof (OA1 AN); clear - H; lia)) as K;
                  destruct K as [k1 k2 k3]; constructor; assumption).
        all: try (pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB4 MU WM ltac:(cbn; clear - SXB; lia) ltac:(intros BN; cbn; pose proof (OB1 BN); clear - H; lia)) as K;
                  destruct K as [k1 k2 k3]; constructor; assumption).
      + clear MU WM CEA4 CEB4. pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
        zstep. zstep. zstep. zstep.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        match goal with MI5 : mem_inv usegs m5, CX5 : rw_cells usegs m5 X _ |- _ =>
          pose proof (xj_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ 1 J4 MU WM MI5 CX5 ltac:(left; reflexivity)) as J5 end.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
        eapply KCL; [exact J5| | | | left; reflexivity| right; right; reflexivity].
        * pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA4 MU WM ltac:(cbn; clear - SXA; lia) ltac:(intros AN; cbn; pose proof (OA1 AN); clear - H; lia)) as K.
          destruct K as [k1 k2 k3]; constructor; assumption.
        * pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB4 MU WM ltac:(cbn; clear - SXB; lia) ltac:(intros BN; cbn; pose proof (OB1 BN); clear - H; lia)) as K.
          destruct K as [k1 k2 k3]; constructor; assumption.
        * match goal with FR5 : rw_cells usegs m5 (bv_unsigned sp - 112) FRL |- _ => exact FR5 end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_LSET : forall (i j : Z) (t0 t1 t2 raj a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 t3 t4 t5 t6 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (sg nXc pXc : Z) (xs : list word) (own : limb_own),
    XJ0 hc LBc mc moc (mkMPD X sg nXc pXc xs padX own) ->
    BJE dA LBc mc (mkMPD X sg nXc pXc xs padX own) -> BJE dB LBc mc (mkMPD X sg nXc pXc xs padX own) ->
    rw_cells usegs mc (bv_unsigned sp - 112) FRL ->
    0 <= i <= nA -> 0 <= j <= nB -> i + j <= nXc ->
    aevtM usegs moc POST (MS (mkR raj SPJ gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 Ba) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 Aa) (Z_to_bv 64 i) x20 x21 x22 x23 (Z_to_bv 64 (- j)) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20d0c) fc None mc (seg_rom usegs)).
  Proof.
    intros until own. intros J BA BB FRc HI_ HJ HN. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU as SPJU.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *. rewrite Z.sub_0_r in ST1.
    assert (DJ : disjoint_from (mpd_ivs (mkMPD X sg nXc pXc xs padX own)) (bv_unsigned sp - 112) 112).
    { unfold mpd_ivs. cbn [md_addr md_own md_p md_n]. destruct own.
      - cbn [disjoint_from]. split; [clear - XS0 SLO2 HLS ACL0; lia| exact I].
      - flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ _ _ _ _ _ PC _. cbn [disjoint_from].
        split; [clear - XS0 SLO2 HLS ACL0; lia|]. split; [clear - PC SLO2 HLS ACL0; lia| exact I].
      - exfalso. exact (NS1 eq_refl). }
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    zstep. zstep. zstep.
    pose proof (U_mpi_lset_spec L HI HCALLOC HLS SW DIMG HND) as SL. unfold mpi_lset_stmt, U_MPI_LSET in SL.
    eapply aevtM_cut.
    { eapply SL with (dX := mkMPD X sg nXc pXc xs padX own) (z := 0) (lo := lo); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        rewrite ?SPJU; try reflexivity; try eassumption.
      all: try (rewrite <- MSFE; exact CA).
      all: try (clear; lia).
      all: try (clear - SLO2 HLS; lia).
      all: try (rewrite HT1; clear - HTOP; lia).
      all: try (clear - SPA; Z.div_mod_to_equations; lia).
      all: split; [| split; [exact (proj1 (proj2 XW))| exact XP1]].
      all: rewrite HT1; pose proof (xj_cwX _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as CW; cbn [md_addr] in CW |- *; rewrite ?SPJU in CW.
      all: exact CW. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m2 mo2 h2 LB2 dX2 r E PO. injection E as E1 E2. subst ms' mo'.
    rewrite ?SPJU in PO.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 CR.
    replace (ret_pc (Z_to_bv 64 0x20d18)) with (Z_to_bv 64 0x20d18) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    unfold lset_R in CR. flat constr:(CR) 3%nat. flclear CR. intros CR1 CRA CRF.
    assert (BK : binop_keep LBc (mkMPD X sg nXc pXc xs padX own) dX2).
    { split; [exact CRA|]. split; [destruct CR1 as [(_ & _ & _ & _ & _ & K)|(_ & ->)]; [exact K| reflexivity]|].
      split; [exact CRF|]. destruct CR1 as [(_ & K & _)|(_ & ->)]; [rewrite K; cbn [md_n]; apply Z.le_max_l| apply Z.le_refl]. }
    pose proof (xj_call _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J MI2 ltac:(rewrite SPJU, Z.sub_0_r; exact ST2) MF2 HT2 HH2 MX2 OUT2
                  ltac:(rewrite SPJU, Z.sub_0_r; exact HPX2) SOK2 BK) as J2.
    pose proof (bj_call _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ JBA J BA MI2 HH2 MX2 OUT2 ltac:(rewrite SPJU, Z.sub_0_r; exact HPX2) BK) as BA2.
    pose proof (bj_call _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ JBB J BB MI2 HH2 MX2 OUT2 ltac:(rewrite SPJU, Z.sub_0_r; exact HPX2) BK) as BB2.
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp - 112) FRL) by (eapply fr_presx; [exact HPX2| exact FRc| exact DJ]).
    clear MU WM. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    zstep. if_cases KR; zify_cond KR.
    - destruct CR1 as [(-> & CN & CO & _)|(-> & _)]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; first [discriminate KR| lia]].
      destruct dX2 as [X2 sg2 n2 p2 xs2 pad2 own2]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CN, CO, CRA, BK. subst own2.
      flat constr:(BK) 4%nat. intros E1 E2 _ _. cbn [md_addr md_pad] in E1, E2. subst X2 pad2.
      eapply mm_TAIL; [exact J2| exact BA2| exact BB2| exact FR2| exact HI_| exact HJ| rewrite CN; clear - HN; lia].
    - zstep.
      eapply KCL; [exact J2| exact BA2| exact BB2| exact FR2| destruct CR1 as [(-> & _)|(-> & _)]; [left| right]; reflexivity| right; left; reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_G : forall (i j : Z) (t0 t1 t2 raj a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 t3 t4 t5 t6 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (sg nXc pXc : Z) (xs : list word) (own : limb_own),
    XJ0 hc LBc mc moc (mkMPD X sg nXc pXc xs padX own) ->
    BJE dA LBc mc (mkMPD X sg nXc pXc xs padX own) -> BJE dB LBc mc (mkMPD X sg nXc pXc xs padX own) ->
    rw_cells usegs mc (bv_unsigned sp - 112) FRL ->
    0 <= i <= nA -> 0 <= j <= nB -> i + j <= 10000 ->
    aevtM usegs moc POST (MS (mkR raj SPJ gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 Ba) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 Aa) (Z_to_bv 64 i) (Z_to_bv 64 (-16)) (Z_to_bv 64 (i + j)) x22 x23 (Z_to_bv 64 (- j)) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20cb4) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until own. intros J BA BB FRc HI_ HJ HIJ. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU as SPJU.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *. rewrite Z.sub_0_r in ST1.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof JBA as [_ _ _ _ SXA]. pose proof JBB as [_ _ _ _ SXB]. cbn [md_addr] in SXA, SXB.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    zstep. rewrite zx16_small by (clear - NR1; lia).
    zstep. if_cases KG; zify_cond KG; rewrite ?Z.mod_small in KG by (clear - NR1 HI_ HJ HIJ; lia).
    { eapply mm_LSET; [exact J| exact BA| exact BB| exact FRc| exact HI_| exact HJ| clear - KG; lia]. }
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := i + j) (sz := 4) (lo := lo);
      rewrite ?SPJU; try eassumption; try reflexivity; clear - SLO HLS ACL ACP HTOP HT1 HI_ HJ HIJ NR1 SPB; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. injection E as E1 E2. subst ms' mo'.
    rewrite ?SPJU in PO.
    flat constr:(PO) 7%nat. flclear PO. intros MI2 ST2 MF2 HPc h2 HT2 RES2.
    replace (ret_pc (Z_to_bv 64 0x20cc8)) with (Z_to_bv 64 0x20cc8) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    clear MU WM.
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp - 112) FRL).
    { eapply (heap_pres_rw_cells usegs L); [exact HPc| exact FRc| rewrite FRSZ; apply client_range_stack; clear; lia]. }
    assert (BA2 : BJE dA LBc m2 (mkMPD X sg nXc pXc xs padX own)).
    { eapply (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA); [exact J| exact BA| rewrite SPJU, Z.sub_0_r; exact HPc| exact MI2]. }
    assert (BB2 : BJE dB LBc m2 (mkMPD X sg nXc pXc xs padX own)).
    { eapply (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB); [exact J| exact BB| rewrite SPJU, Z.sub_0_r; exact HPc| exact MI2]. }
    destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
    { (* [comment removed for export] *)
      pose proof (xj_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J MI2 ltac:(rewrite SPJU, Z.sub_0_r; exact ST2) MF2 ltac:(rewrite SPJU, Z.sub_0_r; exact HPc) HT2 HH2) as J2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      eapply KCL; [exact J2| exact BA2| exact BB2| exact FR2| right; reflexivity| left; reflexivity]. }
    (* [comment removed for export] *)
    replace ((i + j) * 4) with (4 * (i + j)) in * by (clear; lia).
    destruct (xj_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J MI2 ltac:(rewrite SPJU, Z.sub_0_r; exact ST2) MF2 ltac:(rewrite SPJU, Z.sub_0_r; exact HPc) HT2 HH2 HBA HNEW ltac:(cbn [md_n]; clear - KG HIJ; lia)) as [J2 F2].
    flat constr:(HBA) 5%nat. intros An0 An16 _ AnC AnI. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    clear HPc JX MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 NM1 CX1 AD1 PD1 FRc BA BB.
    pose proof J2 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *. rewrite Z.sub_0_r in ST1.
    flat constr:(MX1) 2%nat. intros (CX2 & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ An0 AnC ACV HIJ HI_ HJ; lia|].
    zstep. zstep. zstep. if_cases KP; zify_cond KP.
    { (* [comment removed for export] *)
      assert (EO : own = LNull).
      { destruct own; [reflexivity| | exfalso; exact (NS1 eq_refl)]. exfalso. flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ N1' _ _ _ P0 PC _. rewrite Z.mod_small in KP by (clear - N1' P0 PC ACV; lia). clear - KP P0. lia. }
      subst own. pose proof (xg_null _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2.
      flat constr:((OWN0 eq_refl)) 2%nat. intros EP EN.
      clear MU WM. pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      clear HH1 HH2 HNEW SOK1 ST2 FR1 HPX1 MI1.
      zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D2 MU WM MI2 CX2) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
      pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ _ _ _ _ D2 BA2 MU WM) as BA5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BA5.
      pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ _ _ _ _ D2 BB2 MU WM) as BB5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BB5.
      match goal with FR5 : rw_cells usegs m5 (bv_unsigned sp - 112) FRL |- _ =>
        eapply mm_LSET; [exact J5| exact BA5| exact BB5| exact FR5| exact HI_| exact HJ| clear; lia] end. }
    (* [comment removed for export] *)
    assert (EO : own = LHeap).
    { destruct own; [| reflexivity| exfalso; exact (NS1 eq_refl)]. exfalso. flat constr:((OWN0 eq_refl)) 2%nat. intros EP _. apply KP. rewrite EP. reflexivity. }
    subst own. flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ N1' XIN XPAL _ P0 PC PI.
    flat constr:((xg_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl)) 9%nat. intros SBY SLEN DST DLEN SEP _ _ _ _.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP.
    clear HH1 HH2 HNEW SOK1 FR1 HPX1.
    zstep. zstep.
    lazymatch goal with |- context [Z.land ?q 3] =>
      let E := fresh "E" in
      assert (E : Z.land q 3 = 0)
        by (rewrite Z.land_lor_distr_l, !land_3_mod'; rewrite ?unsigned_lit by lia;
            replace (pXc mod 4) with 0 by (clear - XPAL; Z.div_mod_to_equations; lia);
            replace (An mod 4) with 0 by (clear - An16; Z.div_mod_to_equations; lia); reflexivity);
      rewrite E; clear E end.
    zstep. if_false.
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof U_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    assert (U1 : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; clear - An0 AnC ACV HIJ HI_ HJ; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 pXc) = pXc) by (apply unsigned_lit; clear - P0 PC ACV N1'; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 (nXc * 4)) = nXc * 4) by (apply unsigned_lit; clear - N1' NR1; lia).
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s xs); rewrite ?U1, ?U2, ?U3;
      [ exact SBY | rewrite SLEN; clear; lia | replace (Z.to_nat (nXc * 4)) with (4 * length (firstn (Z.to_nat nXc) (repeat (Z_to_bv 64 0) (Z.to_nat (i + j)))))%nat by (rewrite DLEN; clear; lia); exact DST
      | clear - SEP; lia | exact MI2 ] | ].
    clear SPc. unfold memcpy_post. cbv beta. intros ms' PO.
    flat constr:(PO) 21%nat. flclear PO. intros z0 z1 z2 za1 za2 z3 z4 z5 z6 z7 z8 z9 z10 z11 m3 E MUd WMd MI3 PA3 _. subst ms'.
    rewrite ?U1, ?U2, ?U3 in MUd. rewrite ?U1, ?U2, ?U3 in PA3.
    replace (ret_pc (Z_to_bv 64 0x20cf4)) with (Z_to_bv 64 0x20cf4) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    replace (An + nXc * 4) with (An + 4 * nXc) in MUd by (clear; lia). replace (Z.to_nat (nXc * 4)) with (Z.to_nat (4 * nXc)) in PA3 by (clear; lia).
    flat constr:((xg_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ J2 F2 eq_refl MUd WMd MI3 PA3)) 2%nat. intros J3 F3. cbn [md_limbs md_n] in F3.
    flat constr:((bj_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ _ _ _ J2 F2 BA2)) 2%nat. intros ESA ELA. cbn [md_addr md_own md_p md_n] in ESA, ELA.
    pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA2 MUd WMd ltac:(cbn; clear - ESA HIJ HI_ HJ KG; lia) ltac:(intros BN; cbn; pose proof (ELA BN); clear - H HIJ HI_ HJ KG; lia)) as BA3.
    flat constr:((bj_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ _ _ _ J2 F2 BB2)) 2%nat. intros ESB ELB. cbn [md_addr md_own md_p md_n] in ESB, ELB.
    pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB2 MUd WMd ltac:(cbn; clear - ESB HIJ HI_ HJ KG; lia) ltac:(intros BN; cbn; pose proof (ELB BN); clear - H HIJ HI_ HJ KG; lia)) as BB3.
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp - 112) FRL).
    { eapply rw_cells_transport; [exact FR2| exact MUd| exact WMd|]. cbn. rewrite FRSZ. clear - AnC ACL0 SLO HLS HIJ HI_ HJ KG NR1. lia. }
    clear J2 F2 BA2 BB2 MU WM DST SBY CX2 ST2 MI2 MK2 MI1 ST1 HT1 MF1 MX1 NS1 OUT1 FRS1 XP1 AD1 PD1 NM1 JX FR2 ESA ELA ESB ELB.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    pose proof J3 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK3.
    flat constr:((xg_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J3 F3 eq_refl)) 4%nat. intros ZIN ZCH ZLEN ZB. cbn [md_p md_n md_limbs] in ZIN, ZCH, ZLEN, ZB.
    (* [comment removed for export] *)
    flat constr:(MX1) 2%nat. intros (CX3 & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
    eapply aevtM_cut.
    { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pXc) (len := 4 * nXc) (lo := lo) (junk := u32s xs);
        rewrite ?SPJU; try eassumption; try reflexivity.
      all: try (right; split; [exact ZIN|]; rewrite <- ZLEN; exact ZCH).
      all: try exact ZB.
      all: try (rewrite Z.sub_0_r in ST1; exact ST1).
      all: try (rewrite HT1; clear - HTOP SPJU; rewrite <- SPJU; lia).
      all: try (rewrite <- MSFE; exact CA).
      all: try (f_equal; clear; lia).
      all: clear - SLO SPA SPB HLS ACL ACP SPJU; try lia. all: Z.div_mod_to_equations; lia. }
    cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m4 mo4 h4 E PO. injection E as -> ->.
    rewrite ?SPJU in PO.
    flat constr:(PO) 7%nat. flclear PO. intros MI4 ST4 MF4 HT4 HH4 PX4 SOK4.
    replace (ret_pc (Z_to_bv 64 0x20d04)) with (Z_to_bv 64 0x20d04) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (xg_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ J3 F3 eq_refl MI4 ltac:(rewrite SPJU, Z.sub_0_r; exact ST4) MF4 HT4 HH4 ltac:(rewrite SPJU, Z.sub_0_r; exact PX4) SOK4) as D4.
    pose proof (bj_zfree _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ _ _ _ _ J3 F3 BA3 eq_refl ltac:(rewrite SPJU, Z.sub_0_r; exact PX4) MI4) as BA4. cbn [md_p] in BA4.
    pose proof (bj_zfree _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ _ _ _ _ J3 F3 BB3 eq_refl ltac:(rewrite SPJU, Z.sub_0_r; exact PX4) MI4) as BB4. cbn [md_p] in BB4.
    assert (FR4 : rw_cells usegs m4 (bv_unsigned sp - 112) FRL).
    { eapply fr_presx; [exact PX4| exact FR3| cbn; clear - PC ACL0 SLO HLS; lia]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    clear J3 F3 BA3 BB3 MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 AD1 PD1 NM1 MU WM MK3 HH4 PX4 ZCH PA3 MUd WMd MI3 SOK4 JX FR3.
    pose proof (xd_struct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D4) as CX4. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX4. unfold mpi_cells in CX4.
    pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    clear SEP PI AnI.
    zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D4 MU WM MI4 CX4) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
    pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ _ _ _ _ D4 BA4 MU WM) as BA5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BA5.
    pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ _ _ _ _ D4 BB4 MU WM) as BB5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BB5.
    match goal with FR5 : rw_cells usegs m5 (bv_unsigned sp - 112) FRL |- _ =>
      eapply mm_LSET; [exact J5| exact BA5| exact BB5| exact FR5| exact HI_| exact HJ| clear; lia] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac scan_open J :=
    pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP;
    pose proof alloc_ceiling_bounds as ACV; pose proof SPJU as SPJU;
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1);
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *;
    pose proof (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI1.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_SUM : forall (i j : Z) (t0 t1 t2 raj a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 t3 t4 t5 t6 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd),
    XJ0 hc LBc mc moc dXc -> BJE dA LBc mc dXc -> BJE dB LBc mc dXc -> rw_cells usegs mc (bv_unsigned sp - 112) FRL ->
    md_addr dXc = X -> md_pad dXc = padX -> 0 <= i <= nA -> 0 <= j <= nB ->
    aevtM usegs moc POST (MS (mkR raj SPJ gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 Ba) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 Aa) (Z_to_bv 64 i) x20 x21 x22 x23 (Z_to_bv 64 (- j)) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20c94) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J BA BB FRc EA EP HI_ HJ. jc_open. scan_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ BA)) 6%nat. intros _ _ _ _ NRA _. flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ BB)) 6%nat. intros _ _ _ _ NRB _.
    cbn [md_n] in NRA, NRB.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    zstep.
    lazymatch goal with |- context [Z_to_bv 64 (i - ?e)] => replace (Z_to_bv 64 (i - e)) with (Z_to_bv 64 (i + j)) by zeq end.
    zstep. zstep. zstep. zstep. if_cases KL; zify_cond KL; rewrite ?Z.mod_small in KL by (clear - HI_ HJ NRA NRB; lia).
    { eapply KCL; [exact J| exact BA| exact BB| exact FRc| right; reflexivity| left; reflexivity]. }
    zstep. chk. zstep. zstep. chk.
    eapply mm_G; [exact J| exact BA| exact BB| exact FRc| exact HI_| exact HJ| clear - KL; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_BLOOP : forall (k : nat) (i : Z) (t0 t1 t2 raj a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 x24 t3 t4 t5 t6 r0 r1 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd) (r : Z),
    r <= Z.of_nat k ->
    XJ0 hc LBc mc moc dXc -> BJE dA LBc mc dXc -> BJE dB LBc mc dXc -> rw_cells usegs mc (bv_unsigned sp - 112) FRL ->
    md_addr dXc = X -> md_pad dXc = padX -> 0 <= i <= nA -> 0 <= r <= nB ->
    r1 = Z_to_bv 64 (- r) -> r0 = Z_to_bv 64 (4 * r - 4) ->
    aevtM usegs moc POST (MS (mkR raj SPJ gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 Ba) r0 r1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 Aa) (Z_to_bv 64 i) x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20c48) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until r; intros Hk J BA BB FRc EA EP HI_ HR -> ->.
    all: jc_open; scan_open J.
    all: flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ BB)) 8%nat; intros B0 B16 BAL LENB NRB BS OWNB0 OWNB1;
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    all: flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BB))) 2%nat; intros (CEB & _) _;
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEB; unfold mpi_cells in CEB.
    all: pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl usegs mc) as WM.
    all: zstep; zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit_wrap in K0.
    2: exfalso; assert (r = 0) by (clear - Hk HR; lia); subst r; revert K0; clear; intro K0; first [ apply K0; reflexivity | vm_compute in K0; first [ discriminate K0 | lia ] ].
    1,2: zstep; eapply mm_SUM with (j := r); [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| exact HI_| clear - HR; lia].
    assert (HR1 : 1 <= r) by (clear - K0 HR; lia).
    assert (BN : ownB <> LNull) by (intros C; (flat constr:((OWNB0 C)) 2%nat; intros _ N0); clear - N0 HR HR1; lia).
    flat constr:((OWNB1 BN)) 5%nat. intros NB1 PB0 PB4 BBY _. rewrite ?SPJU in *.
    pose proof (u32ro_bound _ _ _ _ BBY) as EB.
    zstep. zstep. zstep. chk.
    zstep. zstep. zstep. zstep. chk.
    zstep. chk.
    zstep. zstep. zstep. chk.
    destruct (nth_error zs (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENB HR HR1; lia].
    pose proof (u32ro_read usegs mc pB zs (r - 1) w _ BBY NTH ltac:(clear - HR1; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - eapply IH with (r := r - 1); try eassumption; [clear - Hk; lia| clear - HR HR1; lia| f_equal; clear; lia| f_equal; clear; lia].
    - zstep. eapply mm_SUM with (j := r); [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| exact HI_| clear - HR; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_BENTRY : forall (i : Z) (t0 t1 t2 raj a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 x24 t3 t4 t5 t6 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd),
    XJ0 hc LBc mc moc dXc -> BJE dA LBc mc dXc -> BJE dB LBc mc dXc -> rw_cells usegs mc (bv_unsigned sp - 112) FRL ->
    md_addr dXc = X -> md_pad dXc = padX -> 0 <= i <= nA ->
    aevtM usegs moc POST (MS (mkR raj SPJ gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 Ba) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 Aa) (Z_to_bv 64 i) x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20c2c) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J BA BB FRc EA EP HI_. jc_open. scan_open J.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BB))) 2%nat. intros (CEB & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEB. unfold mpi_cells in CEB.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ BB)) 8%nat. intros B0 B16 BAL _ NRB _ _ _. cbn [md_addr md_n] in B0, B16, BAL, NRB.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl usegs mc) as WM.
    zstep. chk. zstep. zstep. chk.
    zstep. rewrite zx16_small by (clear - NRB; lia). zstep. zstep. zstep. rewrite ?Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    eapply mm_BLOOP with (k := Z.to_nat nB) (r := nB); try eassumption.
    all: first [ clear - NRB; lia | f_equal; rewrite ?Z.mod_small by (clear - NRB; lia); clear; lia | reflexivity ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_ALOOP : forall (k : nat) (t0 t1 t2 raj a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 t3 t4 t5 t6 r0 r1 : word)
      (hc : HST usegs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd) (r : Z),
    r <= Z.of_nat k ->
    XJ0 hc LBc mc moc dXc -> BJE dA LBc mc dXc -> BJE dB LBc mc dXc -> rw_cells usegs mc (bv_unsigned sp - 112) FRL ->
    md_addr dXc = X -> md_pad dXc = padX -> 0 <= r <= nA ->
    r1 = Z_to_bv 64 r -> r0 = Z_to_bv 64 (4 * r - 4) ->
    aevtM usegs moc POST (MS (mkR raj SPJ gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 Ba) r0 r1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 Aa) x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20bc4) fc None mc (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until r; intros Hk J BA BB FRc EA EP HR -> ->.
    all: jc_open; scan_open J.
    all: flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ BA)) 8%nat; intros A0 A16 AAL LENA NRA AS OWNA0 OWNA1;
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    all: flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BA))) 2%nat; intros (CEA & _) _;
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEA; unfold mpi_cells in CEA.
    all: pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl usegs mc) as WM.
    all: zstep; zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit_wrap in K0.
    2: exfalso; assert (r = 0) by (clear - Hk HR; lia); subst r; revert K0; clear; intro K0; first [ apply K0; reflexivity | vm_compute in K0; first [ discriminate K0 | lia ] ].
    1,2: zstep; eapply mm_BENTRY with (i := r); [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| clear - HR; lia].
    assert (HR1 : 1 <= r) by (clear - K0 HR; lia).
    assert (AN : ownA <> LNull) by (intros C; (flat constr:((OWNA0 C)) 2%nat; intros _ N0); clear - N0 HR HR1; lia).
    flat constr:((OWNA1 AN)) 5%nat. intros NA1 PA0 PA4 ABY _. rewrite ?SPJU in *.
    pose proof (u32ro_bound _ _ _ _ ABY) as EB.
    zstep. zstep. zstep. chk.
    zstep. zstep. zstep. zstep. chk.
    zstep. chk.
    zstep. zstep. zstep. chk.
    destruct (nth_error ys (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENA HR HR1; lia].
    pose proof (u32ro_read usegs mc pA ys (r - 1) w _ ABY NTH ltac:(clear - HR1; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - eapply IH with (r := r - 1); try eassumption; [clear - Hk; lia| clear - HR HR1; lia| f_equal; clear; lia| f_equal; clear; lia].
    - zstep. zstep. eapply mm_BENTRY with (i := r); [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| clear - HR; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_AENTRY : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.PdXc,$7.P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R5.R4.R3.R2.R1.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R5.R4.R2.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R6.R5.R3.)P,(11.$2.R6.(<.(=.&40.Vsp,)+70.)VFRL,)P,(13.$8.(2?.R5.)VX,)P,(13.(0.&40.)(30.R6.)VpadX,)(15.$2.R8.VPOST,(16.(17.R1>.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R21.R20.R1?.(;.&40.VX,)(;.&40.VBa,)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(;.&40.VAa,)R15.R14.R13.R12.R11.R10.Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(;.&40.+20;:<.)Vfc,(18.(0.&40.))R9.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J BA BB FRc EA EP. jc_open. scan_open J.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BA))) 2%nat. intros (CEA & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEA. unfold mpi_cells in CEA.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ BA)) 8%nat. intros A0 A16 AAL _ NRA _ _ _. cbn [md_addr md_n] in A0, A16, AAL, NRA.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl usegs mc) as WM.
    zstep. chk. zstep. zstep. chk.
    zstep. rewrite zx16_small by (clear - NRA; lia). zstep. zstep. rewrite ?Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    eapply mm_ALOOP with (k := Z.to_nat nA) (r := nA); try eassumption.
    all: first [ clear - NRA; lia | f_equal; rewrite ?Z.mod_small by (clear - NRA; lia); clear; lia | reflexivity ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End W.

