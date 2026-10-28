(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_mpi_free P_ecp_group_free P_ecp_red P_ecp_mul_mod.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA
  A_mpi_opnd A_mpi_journey A_mpi_journey2 A_mpi_copy A_mpi_bitlen A_mpi_cmp_mpi A_mpi_free A_mpi_shift_r A_ecp_mul_mod A_ecp_journey A_ecp_journey2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_A_ecp_pair () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "Corelib.Init.Datatypes.app"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.ejtmp"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey2.edis"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.EJ"; "EP0.epair"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey2.eslot"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "epair"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "stdpp.bitvector.definitions.bv_unsigned"; "EP.EPI"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "EP.ep_src"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_binop_stmtA_sz"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_intop_stmtA_sz"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_exp_mod_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.exp_mod_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.exp_mod_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.exp_mod_Rsz"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_sw_rhs_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.ej_ext"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_A"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_B"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.grp_nle"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.sw_rhs_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.sw_rhs_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.C24_ECP_SW_RHS"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_mul_mod.mul_mod_R"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_bitlen.mpi_query_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shift_r.mpi_shift_r_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_free.mpi_free_stmtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_mul_mod_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.mm_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.mm_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.C24_ECP_MUL_MOD"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.mm_nz"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_mpi.mpi_cmp_mpi_stmtA"; "Stdlib.ZArith.BinInt.Z.sgn"].


(* [comment removed for export] *)
Lemma ep_blocks_apart_app2 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PL1,(0.$1.)PL2,(0.$1.)Pb1,$1.Pb2,$1.P,(2.(3.$1.R4.R3.))P,(4.$1.R3.R5.)P,(4.$1.R3.R5.)(5.(6.(7.(8.$9.$9.R5.)(:.$9.$9.R5.))(8.$9.$9.R4.))(6.(7.(8.$9.$9.R4.)(:.$9.$9.R4.))(8.$9.$9.R5.)))")
(* [comment removed for export] *).
Proof.
  induction L1 as [|[x y] L1 IH]; cbn; intros L2 b1 b2 H H1 H2; [destruct H1|].
  destruct H as [Hx H]. destruct H1 as [<-|H1].
  - cbn. destruct b2 as [B k]. cbn. apply Hx. apply in_app_iff. right. exact H2.
  - eapply IH; eauto.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L62420035243.5L64969942440.4L6899624530.4 00000800>00BS2FB1n1HS2FB1nS2FB". (* [comment removed for export] *)
Lemma ep_fdata_sub2 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PLF',(0.$1.)Pb,$1.P,(4.$1.R1.(;.R2.))(<.$1.Lfb,$1.(=.(4.$1.R1.R4.)(=.(6.(8.$9.$9.R1.)(8.$9.$9.R3.))(6.(7.(8.$9.$9.R3.)(:.$9.$9.R3.))(7.(8.$9.$9.R1.)(:.$9.$9.R1.))))))")
(* [comment removed for export] *).
Proof.
  induction LF' as [|[FB n] r IH]; intros b Hb; [destruct Hb|].
  cbn [fdata] in Hb. destruct Hb as [E|[E|Hb]].
  - exists (FB, n). split; [left; reflexivity|]. subst b. cbn [fst snd]. split; [lia|]. pose proof (Z.le_min_r 24 n). lia.
  - exists (FB, n). split; [left; reflexivity|]. subst b. cbn [fst snd]. lia.
  - ddestruct (IH b Hb) as (fb & H1 & H2). exists fb. split; [right; exact H1| exact H2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section EP0.
  Local Notation segs := asegs.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA segs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variables (h : HST segs R HIA) (LB LF : list blk) (m : mem) (SP lo FR : Z) (FRAME : list cell) (XO : list ivl) (MC : Z).
  Hypothesis EC : ECA R HIA h LB LF m SP lo FR FRAME XO MC.
  Local Ltac ec_open := pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
  Local Notation EJ0 := (EJ R HIA h LB LF m SP lo FR FRAME XO MC).
  Local Notation TMP := (ejtmp R HIA LB LF).
  Local Notation SLOT := (eslot R HIA h LB LF SP lo XO MC).

  (* [comment removed for export] *)
  Definition epair (hk : HST segs R HIA) (LBk : list blk) (mk : mem) (A1 : Z) (d1 : mpd) (A2 : Z) (d2 : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "(=.(>.VR,VHIA,VLB,VLF,O7.O6.O5.O4.O3.)(=.(>.VR,VHIA,VLB,VLF,O7.O6.O5.O2.O1.)(=.(?.O3.O1.)Pb,$1.P,(4.$1.R1.O6.)(5.(4.$1.R2.VLB,)(4.$1.R2.(3.$1.(10.O3.)(10.O1.)))))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma epair_swap : forall hk LBk mk A1 d1 A2 d2, epair hk LBk mk A1 d1 A2 d2 -> epair hk LBk mk A2 d2 A1 d1.
  Proof.
    (intros hk LBk mk A1 d1 A2 d2 dd_H; ddestruct dd_H as (T1 & T2 & D12 & COV)).
    refine (conj T2 (conj T1 (conj (edis_sym _ _ D12) _))).
    intros b Hb. destruct (COV b Hb) as [K|K]; [left; exact K| right]. rewrite !in_app_iff in *. tauto.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L15756354262.4 L20983884400.5 L28776808227.3 L38713511598.3 L38948636245.0 L40952223775.8 L46798920039.7 L52184379240.5 L52320020432.3 L59657045483.10L9689407360.2  00000>00P00[00f00g01C01X01j02302Q02XS1R2lo3LOS3ALOS2SP2lo2FR3SPc3HSPS2A12A23S12S2MC2A13MS1SS1R2SP2lo2FR3LOS3FR03SPc3HSPS2SP2lo2FR3SLO2A13SL1S2SP2lo2FR3SPc3HSPS2A12dZ1KS1R3HIA1h2SP2lo2FR3FR03SLO1a1SS2dZ2N1". (* [comment removed for export] *)
  #[using="EC"] Lemma epair_call : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.Pm',P,(13.&40.)(14.(13.&8.))Ph',(11.$12.VR,VHIA,)PLB',(0.$1.)Pd1',$15.PSPc,$9.Pdv,$9.Pdf,$9.P,(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R10.R?.R>.R=.R<.)P,(17.R?.R>.R=.R<.R;.R:.R9.)P,(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,R=.)P,(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,R<.)P,(5.(6.(7.R?.+10.)R=.)(6.(7.R=.+10.)R?.))P,(=.(6.Vlo,R8.)(6.R8.(19.VSP,VFR,)))P,(6.=R8.)P,(6.=R8.)P,(1:.$12.R?.)P,(1;.$12.R10.Vlo,(19.VSP,VFR,))P,(1<.$12.VR,(1=.R17.R14.)VLF,R=.(1>.VR,)(1?.$12.VR,VHIA,R18.)(20.(21.$9.$9.)(22.$9.$9.R15.(7.R15.+10.))(23.(21.$9.$9.)))R16.R11.)P,(24.$9.(25.$12.VR,VHIA,R11.)(25.$12.VR,VHIA,R19.))P,(24.$9.(1?.$12.VR,VHIA,R12.)(1?.$12.VR,VHIA,R1:.))P,(24.$9.(26.$12.VR,VHIA,R13.)(26.$12.VR,VHIA,R1;.))P,Px,$9.P,(27.$12.VR,VHIA,R1=.R1.)(27.$12.VR,VHIA,R16.R2.)P,(6.(28.$12.VR,VHIA,R15.)(7.(28.$12.VR,VHIA,R1=.)R11.))P,(6.(29.$12.VR,VHIA,R16.)(7.(29.$12.VR,VHIA,R1>.)R11.))P,(2:.$12.VR,VHIA,R17.R16.VLF,R18.)P,(2;.$12.R19.R17.R16.)P,(2<.R20.R1=.R18.R17.)P,Pb,$1.P,(4.$1.R1.(10.R19.))(5.(4.$1.R2.(10.R20.))(2=.VR,(1=.R23.R20.)VLF,(8.$9.$9.R2.)(:.$9.$9.R2.)))(=.(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,(7.R25.R17.)(7.R24.R16.)R1;.R1:.R1<.)(17.R1;.R1:.R1<.R20.R19.R1>.R1=.))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    intros until df. (intros J dd_H; ddestruct dd_H as (T1 & T2 & D12 & COV); intros dd_H; ddestruct dd_H as (CW1 & SL1 & XI1 & MS1); intros dd_H; ddestruct dd_H as (CW2 & SL2 & _ & _); intros S12 HSP Hdv Hdf MI' ST' HP HT' HS' HF' HCS' HV' HFR' HH' M1' OUT' FRA').
    assert (HSP2 : arl_stklo R <= SPc <= SP) by (clear - HSP LOS FR0; lia).
    assert (CRA : forall A, client_wrange L (LB ++ fdata LF) SP (htop segs R HIA h) A 16 -> client_range L (LB ++ fdata LF) lo A 16).
    { intros A CW a Ha. destruct (CW a Ha) as [S|[D|B]]; [left; clear - S SLO FR0; lia| right; left; exact D| right; right; exact B]. }
    assert (LAP : forall B dZ, TMP hk LBk mk B dZ -> md_own dZ = LHeap -> disjoint_from [(A1, A1 + 16)] (md_p dZ) (4 * md_n dZ)).
    { intros B dZ TZ EO. ddestruct (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk B dZ J TZ EO) as (_ & N1 & _ & _ & _ & _ & FRA).
      destruct (fresh_apart_client R LB LF lo A1 16 _ _ FRA (CRA A1 CW1) ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K|K];
        cbn [disjoint_from fst snd]; (split; [clear - K; lia| exact I]). }
    pose proof (ej_aobj_call R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 m' h' SPc _ J T1 CW1 HSP2 HP HCS') as OA1'.
    pose proof (ej_mc_call R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 m' SPc _ J T1 HP ltac:(cbn [disjoint_from fst snd]; split; [clear - MS1; lia| exact I])) as MC'.
    destruct (ej_call R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 m' h' LB' d1' SPc dv df [(A1, A1 + 16)] J T1
                ltac:(clear - HSP; lia) Hdv Hdf MI' ST' HP XI1 ltac:(cbn [disjoint_from fst snd]; split; [clear - SL1 FR0 SLO; lia| exact I]) ltac:(clear - HSP; lia)
                HT' HS' HF' HCS' HV' HFR' HH' M1' OUT' FRA' OA1' MC') as [J' T1'].
    destruct (ejtmp_keep R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 A2 d2 m' h' LB' d1' SPc _ J T1 T2 D12 CW2 HSP2 HP
                ltac:(cbn [disjoint_from fst snd]; split; [clear - S12; lia| exact I]) (LAP A2 d2 T2) MI' HCS' OUT' M1' FRA') as [T2' D12'].
    split; [exact J'|]. refine (conj T1' (conj T2' (conj D12' _))).
    dpose OUT' as (_ & _ & O3 & _ & O5).
    intros b Hb. destruct (O3 b Hb) as [K1|K1]; [| right; apply in_or_app; left; exact K1].
    destruct (COV b K1) as [K2|K2]; [left; exact K2| right]. rewrite !in_app_iff in *. destruct K2 as [K2|K2]; [left; rewrite (O5 b K2 Hb); exact K2| right; exact K2].
    all: match goal with |- ?g => idtac "PAIR-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="EC"] Lemma epair_scratch : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.Pwlo,$9.Pwhi,$9.Pm',P,(13.&40.)(14.(13.&8.))P,(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R<.R;.R:.R9.R8.)P,(17.R;.R:.R9.R8.R7.R6.R5.)P,(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,R9.)P,(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,R8.)P,(2>.(20.(21.$9.$9.)(22.$9.$9.R7.R6.)(23.(21.$9.$9.)))R<.R5.)P,(2?.$12.R=.R6.)P,(1:.$12.R7.)P,(1;.$12.R8.Vlo,(19.VSP,VFR,))P,(2:.$12.VR,VHIA,R12.R11.VLF,R9.)P,(6.Vlo,R<.)P,(6.R<.(19.VSP,VFR,))(=.(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R17.R16.R15.R14.R<.)(17.R15.R14.R<.R12.R11.R10.R?.))")
(* [comment removed for export] *).
  Proof.
    intros until m'. (intros J dd_H; ddestruct dd_H as (T1 & T2 & D12 & COV); intros dd_H; ddestruct dd_H as (_ & SL1 & _); intros dd_H; ddestruct dd_H as (_ & SL2 & _); intros MU WM MI' ST' HH' W1 W2).
    destruct (ej_scratch R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 wlo whi m' J T1 SL1 MU WM MI' ST' HH' W1 W2) as [J' T1'].
    split; [exact J'|].
    refine (conj T1' (conj (ejtmp_scratch R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A2 d2 wlo whi m' J T2 SL2 MU WM W1 W2) (conj D12 COV))).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L10633144206.3 L10678603361.3 L12214810855.7 L2333536794.11 L24355732615.5 L25182671526.8 L26791175961.6 L28006323098.1 L32245819379.8 L37272752416.6 L38948636245.0 L48510416333.8 L52037001354.10L5246360089.2  L58422693159.4 L60098763854.3 L60482097787.6 L6064815669.3  L61896008187.3 L66566358642.6 00000900D00\01?01Q01l02@02D02`03003103N03m04404>04H04\04e04m05@S2d11a2HaS2SP2FR3FR0S1R2SP2lo2FR3LOS3FR03SLOS1R3HIA1h2SP2lo2FR3LOS3FR03TOP1a2HaS2SP2lo2FR2MC4MCLOS1R2SP2lo2FR3LOS3ALO2dd3PCdS2SP2lo2FR3FR01A3SLAS2d1S1R2SP2lo2FR3LOS3FR03SLO3ALOS1R3HIA1h2SP1a1SSS1R2MC3DI13DI23MC13MC22d13PI1S1R2SP2lo2FR3LOS3SLO3ALO2d13PC1S2d12N1S2SP2lo2FRS1R2lo3LOSS1R3HIA1h2SP2lo4SPHIS2d12dd1KS2d11A1KS2SP2lo2FR3FR01x2Hx". (* [comment removed for export] *)
  #[using="EC"] Lemma epair_limbs : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.Pm',P,(13.&40.)(14.(13.&8.))Pxs',(0.(13.&40.))P,(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R;.R:.R9.R8.R7.)P,(17.R:.R9.R8.R7.R6.R5.R4.)P,(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,R8.)P,(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,R7.)P,(24.$30.(31.R9.)$32.)P,(2>.(20.(21.$9.$9.)(22.$9.$9.Vlo,(19.VSP,VFR,))(20.(21.$9.$9.)(22.$9.$9.(33.R:.)(7.(33.R:.)(34.+4.(35.R:.))))(23.(21.$9.$9.))))R<.R7.)P,(2?.$12.R=.R8.)P,(1:.$12.R9.)P,(1;.$12.R:.Vlo,(19.VSP,VFR,))P,(2;.$12.R;.R11.(36.(37.R>.)(38.R>.)(35.R>.)(33.R>.)R:.(39.R>.)(31.R>.)))(=.(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R15.R14.R13.R12.R<.)(17.R13.R12.R<.R10.(36.(37.R?.)(38.R?.)(35.R?.)(33.R?.)R;.(39.R?.)(31.R?.))R>.R=.))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    intros until xs'. intros J T S1 S2 EO MU WM MI' ST' MX'.
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk [ck MCk] STk FRk].
    dpose T as (T1 & T2 & D12 & COV). dpose T1 as (MY1 & EA1 & NS1 & FRS1 & OA1).
    ddestruct (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 J T1 EO) as (IN1 & N1 & P01 & PC1 & PI1 & NIN1 & FRA1).
    pose proof (hcs_ok segs R HIA hk) as CSOK.
    set (W := [(lo, SP - FR); (md_p d1, md_p d1 + 4 * md_n d1)]) in *.
    assert (SCS : crange (hcs segs R HIA hk) lo (SP - lo)).
    { eapply crange_sub; [exact (hcs_stack segs R HIA hk)| clear - LOS; lia| rewrite HSk; clear - SPHI; lia]. }
    assert (WC : w_client (hcs segs R HIA hk) W).
    { unfold w_client, W. apply Forall_cons; [cbn [fst snd]; intros x Hx; apply SCS; clear - Hx FR0; lia|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (md_p d1 + 4 * md_n d1 - md_p d1) with (4 * md_n d1) by (clear; lia).
      eapply aobj_crange. eapply hm_aobj_block; [exact HHk| exact IN1]. }
    assert (HH' : HM segs R HIA hk LBk LF m').
    { eapply (hm_munch segs R HIA hk LBk LF W mk m' HHk MU WM). unfold W.
      apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; rewrite HTk; clear - Ha LOS TOP FR0; lia|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. right. right.
      exists (md_p d1, 4 * md_n d1). split; [apply in_or_app; left; exact IN1| cbn [fst snd]; clear - Ha; lia]. }
    assert (DMCW : disjoint_from W MC 8).
    { unfold W. cbn [disjoint_from fst snd]. ddestruct MCOK as (MC1 & MC2 & _). destruct DIMG as [DI1 DI2].
      split; [clear - MCLO; lia| split; [clear - PI1 MC1 MC2 DI1 DI2; lia| exact I]]. }
    assert (DSLOT : forall A, SLOT A -> disjoint_from W A 16).
    { (intros A dd_H; ddestruct dd_H as (CWA & SLA & _ & _)). unfold W. cbn [disjoint_from fst snd].
      assert (CRA : client_range L (LB ++ fdata LF) SP A 16).
      { intros a Ha. destruct (CWA a Ha) as [S|[D|Bk]]; [left; clear - S; lia| right; left; exact D| right; right; exact Bk]. }
      pose proof (fresh_apart_client R LB LF SP A 16 _ _ FRA1 CRA ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS SLO FR0; lia)) as K.
      split; [clear - SLA FR0; lia| split; [clear - K; lia| exact I]]. }
    assert (DTMP : forall A dd, TMP hk LBk mk A dd -> edis d1 dd -> SLOT A -> TMP hk LBk m' A dd).
    { intros A dd TT DD SA. dpose TT as (MY & EA & NS & FRS & OA).
      split; [| split; [exact EA| split; [exact NS| split; [exact FRS|]]]].
      - eapply mpd_at_munch_any; [exact MY| exact MU| exact WM| rewrite EA; exact (DSLOT A SA)|].
        intros ON. assert (EOd : md_own dd = LHeap) by (destruct (md_own dd); [exfalso; exact (ON eq_refl)| reflexivity| exfalso; exact (NS eq_refl)]).
        ddestruct (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A dd J TT EOd) as (INd & Nd & P0d & PCd & _).
        destruct (hm_apart segs R HIA hk LBk LF mk HHk) as [_ BA].
        pose proof (blocks_apart_in2 (LBk ++ LF) _ _ _ _ BA ltac:(apply in_or_app; left; exact IN1) ltac:(apply in_or_app; left; exact INd) (DD EO EOd)) as K.
        unfold W. cbn [disjoint_from fst snd]. split; [clear - PCd ALO LOS; lia| split; [clear - K; lia| exact I]].
      - eapply (aobj_munch segs AL _ CSOK W mk m'); [exact WC| exact MU| exact OA]. }
    split.
    - constructor; try assumption.
      + eapply presA_trans; [exact PXk|]. apply presA_nil_any.
        eapply (presA_drop_fresh segs R HIA h LB LF [] (md_p d1) (4 * md_n d1) mk m' SP); [| exact FRA1| clear - LOS SLO FR0; lia].
        eapply (presA_drop_below segs R HIA h LB LF _ lo (SP - FR) m mk m' SP HH); [| clear - FR0; lia| exact LOS].
        rewrite <- HSk.
        eapply presA_weaken; [| exact SUBk| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x Hx; exact Hx].
        eapply (presA_of_munch segs R LBk LF SP (arl_stklo R) (hstkhi segs R HIA hk) W mk m' (hcs segs R HIA hk) CSOK); [exact WC| | exact MU| exact WM].
        intros c0 Hc. eapply cshd_hcs; [exact HHk| apply Z.le_refl| exact Hc].
      + exists ck. eapply rw_cells_transport; [exact MCk| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. exact DMCW.
      + eapply rw_cells_transport; [exact FRk| exact MU| exact WM|]. rewrite FSZ. unfold W. cbn [disjoint_from fst snd].
        split; [clear - FR0; lia| split; [clear - PC1 ALO LOS SLO FR0; lia| exact I]].
    - split.
      + split; [exact MX'|]. cbn [md_addr md_own]. split; [exact EA1|]. split; [exact NS1|]. split.
        * intros b Hb. apply FRS1. unfold mpd_blk in *. cbn [md_own md_p md_n] in Hb. exact Hb.
        * eapply (aobj_munch segs AL _ CSOK W mk m'); [exact WC| exact MU| exact OA1].
      + split; [exact (DTMP A2 d2 T2 D12 S2)|].
        split; [intros O1 O2; cbn [md_p]; exact (D12 EO O2)|].
        intros b Hb. destruct (COV b Hb) as [K|K]; [left; exact K| right]. unfold mpd_blk in *. cbn [md_own md_p md_n]. exact K.
    all: match goal with |- ?g => idtac "LIMBS-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L13314332586.3 L15756354262.4 L30779775326.6 L31998862047.6 L38948636245.0 L39298475913.2 L39596998220.3 L50504111031.3 L5246360089.2  L53337563057.3 L54376077431.3 L55095140251.3 L59657045483.1000000900G00]01101201901B01K01R01[01f01o02MS2A12d21KS1R2lo3LOS3ALOS2SP2lo2A23SPc3SL23HSPS1R2lo3LOS3ALO2d22B2SS2d22N2S2d12A21KS2d12d21KS2d12N1S2A12d21KS2A12A23S12S2d12A21KS1R3HIA1h2SP2lo2FR3FR03SLO1a1S". (* [comment removed for export] *)
  #[using="EC"] Lemma epair_opnd2 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.PSPc,$9.P,(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R:.R9.R8.R7.R6.)P,(17.R9.R8.R7.R6.R5.R4.R3.)P,(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,R7.)P,(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,R6.)P,(5.(6.(7.R9.+10.)R7.)(6.(7.R7.+10.)R9.))P,(=.(6.Vlo,R6.)(6.R6.VSP,))(=.(2;.$12.R<.R=.R8.)(=.(3:.R:.R8.)(=.(3;.(24.$9.(37.R:.)(37.R8.)))(=.(3<.R:.R8.Vlo,R7.)(=.(3=.(3>.VR,)(3.$1.R=.(;.VLF,))Vlo,(37.R8.)+10.)(=.P,(24.$30.(31.R8.)$32.)(3=.(3>.VR,)(3.$1.R>.(;.VLF,))Vlo,(33.R9.)(34.+4.(35.R9.)))(=.(3?.$12.(40.VR,)(27.$12.VR,VHIA,R>.)R<.R8.)(41.R8.))))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    (intros v f hk LBk mk A1 d1 A2 d2 SPc J dd_H; ddestruct dd_H as (T1 & T2 & D12 & COV); intros dd_H; ddestruct dd_H as (CW1 & SL1 & _ & _); intros dd_H; ddestruct dd_H as (CW2 & SL2 & _ & _); intros S12 HSP).
    ddestruct (ej_opY R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A2 d2 SPc J T2 CW2 SL2 HSP) as (M2 & NS2 & EA2 & _ & CR2 & CRL2 & _ & _ & AO2 & IM2).
    dpose T1 as (M1 & EA1 & NS1 & _ & _).
    pose proof (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 J T1) as BLK1.
    pose proof (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A2 d2 J T2) as BLK2.
    assert (CRA : forall A, client_wrange L (LB ++ fdata LF) SP (htop segs R HIA h) A 16 -> client_range L (LB ++ fdata LF) lo A 16).
    { intros A CW a Ha. destruct (CW a Ha) as [S|[D|B]]; [left; clear - S SLO FR0; lia| right; left; exact D| right; right; exact B]. }
    assert (OWH : forall dd, md_own dd <> LStatic -> md_own dd <> LNull -> md_own dd = LHeap)
      by (intros dd NS ON; destruct (md_own dd); [exfalso; exact (ON eq_refl)| reflexivity| exfalso; exact (NS eq_refl)]).
    split; [exact M2|]. split; [right; rewrite EA1, EA2; exact S12|]. split; [rewrite EA1, EA2; clear - S12; lia|].
    split.
    { unfold opnd_sep. rewrite EA1, EA2.
      split.
      { intros ON. ddestruct (BLK2 (OWH d2 NS2 ON)) as (_ & N2 & _ & _ & _ & _ & FRA).
        destruct (fresh_apart_client R LB LF lo A1 16 _ _ FRA (CRA A1 CW1) ltac:(clear; lia) ltac:(clear - N2; lia) ltac:(clear - ALO LOS; lia)) as [K|K]; [right| left]; clear - K; lia. }
      split.
      { intros EO. ddestruct (BLK1 EO) as (_ & N1 & _ & _ & _ & _ & FRA).
        destruct (fresh_apart_client R LB LF lo A2 16 _ _ FRA (CRA A2 CW2) ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K|K]; [right| left]; clear - K; lia. }
      split.
      { destruct (md_own d1) eqn:O1; [right; left; discriminate| | exfalso; exact (NS1 eq_refl)].
        destruct (md_own d2) eqn:O2; [right; right; left; reflexivity| | exfalso; exact (NS2 eq_refl)].
        destruct (BLK1 eq_refl) as (IN1 & _). destruct (BLK2 eq_refl) as (IN2 & _).
        destruct (hm_apart segs R HIA hk LBk LF mk (ej_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)) as [_ BA].
        pose proof (blocks_apart_in2 (LBk ++ LF) _ _ _ _ BA ltac:(apply in_or_app; left; exact IN1) ltac:(apply in_or_app; left; exact IN2) (D12 O1 O2)) as K.
        right; right; right. clear - K. lia. }
      split; [clear - SL2 HSP; lia|].
      intros ON. ddestruct (BLK2 (OWH d2 NS2 ON)) as (_ & _ & _ & B2 & _). left. clear - B2 ALO LOS. lia. }
    split; [rewrite EA2; exact CR2|]. split; [exact CRL2|]. split; [exact AO2| exact IM2].
    all: match goal with |- ?g => idtac "OPND2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End EP0.

Section EP.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variable MT : list modp_ent.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (SP lo FR : Z) (FRAME : list cell) (XO : list ivl) (MC : Z).
  Hypothesis EC : ECA R HIA h LB LF m SP lo FR FRAME XO MC.
  Variables (gp tp fpw : word) (F : bvmap 5 word) (fc : bv 32) (dd slo STKMAX : Z).
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis D0 : 0 <= dd.
  Hypothesis SP64 : SP < 2^64.
  Hypothesis SPA : (SP - FR) mod 16 = 0.
  Hypothesis SLOK : lo <= SP - FR - STKMAX - arl_need_ecp R.
  Hypothesis STK0 : 0 <= STKMAX.
  Hypothesis UW0 : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned fpw) SP dd.
  Hypothesis XOUW : 28 <= dd \/ forall a, SP <= a < hstkhi asegs R HIA h -> outside XO a.
  Hypothesis SSH : sshad asegs AL m slo SP.
  Hypothesis SLO1 : arl_stklo R <= slo.
  Hypothesis SLO3 : slo <= lo.

  Local Ltac ec_open := pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
  Local Notation EJ0 := (EJ R HIA h LB LF m SP lo FR FRAME XO MC).
  Local Notation TMP := (ejtmp R HIA LB LF).
  Local Notation SLOT := (eslot R HIA h LB LF SP lo XO MC).
  Local Notation PAIR := (epair R HIA LB LF).
  Local Notation SP' := (Z_to_bv 64 (SP - FR)).

  (* [comment removed for export] *)
  Definition EPI (v f : Z) (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (A1 : Z) (d1 : mpd) (A2 : Z) (d2 : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "(=.(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,O9.O8.O7.O6.O5.)(=.(42.VR,VHIA,VLB,VLF,O7.O6.O5.O4.O3.O2.O1.)(=.(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,O4.)(=.(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,O2.)(=.(5.(6.(7.O4.+10.)O2.)(6.(7.O2.+10.)O4.))(=.(43.VR,O4.+10.Vdd,)(43.VR,O2.+10.Vdd,)))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L28776808227.300000;S2A12A23S12". (* [comment removed for export] *)
  #[using="Type"] Lemma epi_swap : forall v f hk LBk mk A1 d1 A2 d2, EPI v f hk LBk mk A1 d1 A2 d2 -> EPI v f hk LBk mk A2 d2 A1 d1.
  Proof.
    (intros v f hk LBk mk A1 d1 A2 d2 dd_H; ddestruct dd_H as (J & P & S1 & S2 & S12 & U1 & U2)).
    refine (conj J (conj (epair_swap R HIA LB LF hk LBk mk A1 d1 A2 d2 P) (conj S2 (conj S1 (conj _ (conj U2 U1)))))). clear - S12. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L19002855022.8 L27060170164.10L27060170164.8 L27060299542.4 L30209986421.10L30209986421.8 L65097143157.8 L66151427842.17L67772674380.10L67772674380.5 L67772674380.8 L67772808174.4 00000=00>00?00O01:01;01]02:02;02<02=02>S1R5NEEDR3NERFFS2SP2FR4SP643FR0S1R2SP2lo2FR6STKMAX4SLOK4STK05NEEDR3LO03NERFS1R2SP2lo2FR6STKMAX4SLOK5NEEDR3NERS2SP2FR2r03SPA1q1r1H2H02q02H4FFFF". (* [comment removed for export] *)
  #[using="HIA h LB LF m FRAME XO MC EC SP64 SPA SLOK STK0"] Lemma ep_base : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "(=.(6.=Vlo,)(=.(6.Vlo,(19.(19.VSP,VFR,)VSTKMAX,))(=.(=.(6.=(19.VSP,VFR,))(44.(19.VSP,VFR,)(45.+2.+40.)))(=.(6.=(46.VR,))(=.(6.(1>.VR,)Vlo,)(24.$9.(47.(19.VSP,VFR,)+8.)=))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    pose proof (arl_need_ecp_rt R) as NER.
    repeat split; try assumption; first [clear - SLOK NER NEEDR; lia | clear - SLOK NER NEEDR LO0 STK0; lia | clear - SP64 FR0; lia | clear - NER NEEDR; lia | clear - SPA; Z.div_mod_to_equations; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L10678603361.3 L11681438613.15L37275290198.6 L56759386243.14L59309024491.6 00000;00k01<01n02?S2SP2FR3FR0S1R3HIA1h2SP2lo2FR6STKMAX4STK03LOS3FR04LOSP1a2HaS1R3HIA1h2SP1a2HaS1R3HIA1h2SP2lo2FR6STKMAX4STK03FR03LO04LOSP1a2Ha1KS1R3HIA1h2HT1K2SH". (* [comment removed for export] *)
  #[using="EC STKMAX SP64 SPA SLOK STK0 UW0 XOUW"] Lemma ep_uwc : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))P,(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R5.R4.R3.R2.R1.)(48.$12.R2.(1>.VR,)(1?.$12.VR,VHIA,R4.)(49.&40.Vfpw,)(19.VSP,VFR,)Vdd,)")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    dpose ep_base as (_ & LOSP & SPR & NE0 & _ & _).
    intros v f hk LBk mk J. rewrite (ej_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J).
    destruct XOUW as [D28|XOUT]; [apply uwc_cap; exact D28|].
    eapply uwc_floor; [| instantiate (1 := SP); clear - FR0; lia].
    eapply uwc_transport; [exact UW0|]. intros a Ha.
    pose proof (hcs_stack asegs R HIA h) as SCS. pose proof (hm_top asegs R HIA h LB LF m HH) as HT.
    destruct (hcs_app asegs R HIA h _ _ SCS ltac:(clear - HT LOS LOSP TOP STK0 FR0 Ha; lia)) as [[_ K]|[_ K]]; [pose proof (art_stk_high asegs R HIA) as SH; exfalso; clear - K SH HT; lia|].
    destruct (ej_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as [PX _].
    refine (proj1 (PX a ltac:(clear - Ha LO0 LOSP K STK0 FR0; lia) ltac:(left; clear - Ha; lia) _)).
    apply XOUT. exact Ha.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L30404892540.700000OS2SP2lo2FR6STKMAX4STK03FR04LOSP". (* [comment removed for export] *)
  #[using="EC STKMAX SP64 SPA SLOK STK0"] Lemma ep_out : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.P,(4:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(=.(2;.$12.R6.R7.R4.)(=.(3;.(24.$30.(31.R4.)$4;.))(=.(24.$9.(37.R4.)R5.)(=.(3<.R4.R4.Vlo,(19.VSP,VFR,))(=.(3=.(3>.VR,)(3.$1.R7.(;.VLF,))Vlo,R5.+10.)(=.P,(24.$30.(31.R4.)$32.)(3=.(3>.VR,)(3.$1.R8.(;.VLF,))Vlo,(33.R5.)(34.+4.(35.R5.)))(=.(4<.VR,R7.VLF,(19.VSP,VFR,)(25.$12.VR,VHIA,R8.)R4.)(=.P,(3;.(24.$30.(31.R4.)$4=.))(5.(6.(7.(33.R5.)(34.+4.(35.R5.)))Vlo,)(6.(19.VSP,VFR,)(33.R5.)))(=.(3?.$12.(40.VR,)(27.$12.VR,VHIA,R8.)R6.R4.)(41.R4.))))))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (_ & LOSP & _).
    (intros v f hk LBk mk A1 d1 A2 d2 dd_H; ddestruct dd_H as (J & (T1 & _) & (CW1 & SL1 & _) & _)).
    exact (ej_opY R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 (SP - FR) J T1 CW1 SL1 ltac:(clear - LOSP STK0 FR0; lia)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ep_src (A1 : Z) (d1 d2 e : mpd) : Prop := e = d1 \/ e = d2 \/ ej_ext R HIA h LB LF m SP lo XO A1 e.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L30404892540.700000OS2SP2lo2FR6STKMAX4STK03FR04LOSP". (* [comment removed for export] *)
  #[using="IMG EC STKMAX SP64 SPA SLOK STK0"] Lemma ep_opnd : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.Pe,$15.P,(4:.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(4>.R6.R5.R3.R2.)(=.(2;.$12.R8.R9.R3.)(=.(3:.R6.R3.)(=.(3<.R6.R3.Vlo,(19.VSP,VFR,))(=.(3=.(3>.VR,)(3.$1.R9.(;.VLF,))Vlo,(37.R3.)+10.)(=.P,(24.$30.(31.R3.)$32.)(3=.(3>.VR,)(3.$1.R:.(;.VLF,))Vlo,(33.R4.)(34.+4.(35.R4.)))(=.(3?.$12.(40.VR,)(27.$12.VR,VHIA,R:.)R8.R3.)(=.(41.R3.)(5.(24.$15.R3.R6.)(3;.(24.$9.(37.R6.)(37.R3.)))))))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (_ & LOSP & _).
    intros v f hk LBk mk A1 d1 A2 d2 e S [E|[E|EX]].
    - subst e. ddestruct (ep_out v f hk LBk mk A1 d1 A2 d2 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
      split; [exact XM|]. split; [left; reflexivity|]. split; [exact XOS|]. split; [rewrite XAD; exact XCR|]. split; [exact XCRL|]. split; [exact XAO|]. split; [exact XIM| left; reflexivity].
    - subst e. ddestruct S as (J & P & S1 & S2 & S12 & _).
      ddestruct (epair_opnd2 R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 A2 d2 (SP - FR) J P S1 S2 S12 ltac:(clear - LOSP STK0 FR0; lia))
        as (M2 & SEP & NE & OS & CR & CRL & AO & IM).
      split; [exact M2|]. split; [exact SEP|]. split; [exact OS|]. split; [exact CR|]. split; [exact CRL|]. split; [exact AO|]. split; [exact IM| right; exact NE].
    - ddestruct S as (J & (T1 & _) & _).
      ddestruct (ej_opE R HIA IMG h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 e (SP - FR) J T1 EX ltac:(clear - LOSP STK0 FR0; lia)) as (EM & ESEP & ENE & EOS & ECR & ECRL & EAO).
      split; [exact EM|]. split; [exact ESEP|]. split; [exact EOS|]. split; [exact ECR|]. split; [exact ECRL|]. split; [exact EAO|].
      ddestruct EX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & IME). split; [exact IME| right; exact ENE].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="EC"] Lemma ep_cnt24 : forall v f hk LBk mk A1 d1 A2 d2, EPI v f hk LBk mk A1 d1 A2 d2 -> cnt24 LBk <= cnt24 LB + 2.
  Proof.
    (intros v f hk LBk mk A1 d1 A2 d2 dd_H; ddestruct dd_H as (J & (_ & _ & _ & COV) & _)).
    pose proof (ej_cnt24 R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk [d1; d2] J) as C.
    cbn [flat_map length app] in C. rewrite app_nil_r in C. specialize (C COV). cbn in C. exact C.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L39570337372.900000XS2SP2lo2FR3slo6STKMAX4STK04SLO34LOSP3FR0". (* [comment removed for export] *)
  #[using="EC STKMAX SP64 SPA SLOK STK0 SSH SLO1 SLO3"] Lemma ep_sshad : forall v f hk LBk mk, EJ0 v f hk LBk mk -> sshad asegs AL mk slo (SP - FR).
  Proof.
    dpose ep_base as (_ & LOSP & _ & _ & _ & M8). ec_open.
    intros v f hk LBk mk J.
    pose proof (ej_sshad R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk slo J SSH SLO1) as SSk.
    exact (proj1 (sshad_split asegs AL mk slo (SP - FR) SP SSk ltac:(clear - SLO3 LOSP STK0 FR0; lia) M8)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L56329741247.600000KS2SP2lo2FR6STKMAX4STK04LOSP". (* [comment removed for export] *)
  #[using="EC STKMAX SP64 SPA SLOK STK0"] Lemma ep_after : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.Pdv,$9.Pdf,$9.PRr,P,$9.P,$15.SpPRET,$9.Pc1,(13.&40.)Pc2,(13.&40.)Pc3,(13.&40.)Pc4,(13.&40.)Pc5,(13.&40.)Pc6,(13.&40.)Pc7,(13.&40.)Pc8,(13.&40.)Pc9,(13.&40.)Pc10,(13.&40.)Pc11,(13.&40.)PQ,P,$4?.SpP,(4:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)P,(6.=R11.)P,(6.=R11.)P,(=.(6.=R10.)(44.R10.(45.+2.+40.)))P,(24.$9.(47.R11.+2.)=)P,Ph',(11.$12.VR,VHIA,)PLB',(0.$1.)Pm',P,(13.&40.)(14.(13.&8.))Pd1',$15.Pr,$9.Pt0',(13.&40.)Pt1',(13.&40.)Pt2',(13.&40.)Pa1',(13.&40.)Pa2',(13.&40.)Pa3',(13.&40.)Pa4',(13.&40.)Pa5',(13.&40.)Pa6',(13.&40.)Pa7',(13.&40.)Pt3',(13.&40.)Pt4',(13.&40.)Pt5',(13.&40.)Pt6',(13.&40.)P,(4:.(7.R31.R28.)(7.R30.R27.)R13.R12.R11.R2<.R10.R2:.R29.)P,A2.R27.R10.R11.(50.$12.(51.$12.VR,VHIA,R15.Vmo,)R1;.(52.(53.(54.&40.R27.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R26.(54.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R6.R5.R4.R3.)VF,(54.&40.R27.)Vfc,(55.(13.&40.))R13.(56.$12.)))Pms',$57.Pmo',$58.P,(<.$58.Lmo1,$58.(=.(51.$12.VR,VHIA,R20.Vmo,R1.)(59.$12.VR,VHIA,(54.&40.R16.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,Vfpw,R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.VF,Vfc,R20.R1?.VLF,R1<.R17.R19.R18.Vlo,R1>.R1.(5:.R3.R2.))))(5;.$12.R:.(5:.R3.R2.))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    intros until Q. (intros S Hdv Hdf HRET HRE K ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & GR).
    injection E as E1 E2. subst ms' mo'.
    ddestruct S as (J & P & S1 & S2 & S12 & U1 & U2). dpose P as ((_ & EA1 & _) & _).
    rewrite ?(unsigned_lit (SP - FR)) in ST2, HP2 by exact SPR. rewrite EA1 in HP2.
    rewrite (ret_pc_even RET HRET HRE).
    destruct (epair_call R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 A2 d2 m2 h2 LB2 dX2 (SP - FR) dv df
                J P S1 S2 S12 ltac:(clear - LOSP STK0; lia) Hdv Hdf MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 FRA2) as [J2 P2].
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [| exact GR].
    exact (conj J2 (conj P2 (conj S1 (conj S2 (conj S12 (conj U1 U2)))))).
    all: match goal with |- ?g => idtac "AFTER-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L12760872139.7 L22358645037.8 L29691610218.12L49959034121.5 L63494745103.1100000G00j01P01f02HS1R3HIA1h2SP2FR3FR03TOPS1R2SP2lo2FR6STKMAX4SLOK5STACK4HSTKS1R3HIA1h2dd3FRC1f2hk2d12eA2eB2HF4HFRkS2LB3C243LBk4HC244C24kS1R3HIA1h3PHI1v2hk2d12eA2eB2HV3HVk". (* [comment removed for export] *)
  #[using="IMG EC slo TPV SP64 SPA SLOK STK0 UW0 XOUW"] Lemma ep_binop : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PENTRY,$9.PSTACK,$9.PNF,$5<.PC24,$9.PPHI,P,$15.P,$15.P,$15.$9.PFRC,P,$15.P,$15.P,$15.P,$9.$9.PRr,P,(0.$1.)P,$15.P,$15.P,$15.P,$9.P,$15.SpP,(5=.$12.VR,VHIA,R7.R6.R5.R4.$5>.$5>.R3.R2.R1.)Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.PeA,$15.PeB,$15.PRET,$9.Pxt0,(13.&40.)Pxt1,(13.&40.)Pxt2,(13.&40.)Pc1,(13.&40.)Pxa0,(13.&40.)Pxa1,(13.&40.)Pxa2,(13.&40.)Pxa3,(13.&40.)Pxa4,(13.&40.)Pxa5,(13.&40.)Pxa6,(13.&40.)Pxa7,(13.&40.)Pc2,(13.&40.)Pc3,(13.&40.)Pc4,(13.&40.)Pc5,(13.&40.)Pc6,(13.&40.)Pc7,(13.&40.)Pc8,(13.&40.)Pc9,(13.&40.)Pc10,(13.&40.)Pc11,(13.&40.)Pxt3,(13.&40.)Pxt4,(13.&40.)Pxt5,(13.&40.)Pxt6,(13.&40.)PQ,P,$4?.SpP,(4:.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)P,(4>.R23.R22.R20.R1?.)P,(4>.R24.R23.R21.R1?.)P,(3:.R21.R20.)P,(43.VR,(37.R22.)+10.Vdd,)P,(43.VR,(37.R22.)+10.Vdd,)P,(6.R34.VSTKMAX,)P,(5?.(60.(61.$1.VLF,)R34.)#200.)P,(6.=A3.R33.R29.R26.R25.)P,(6.=A4.R33.R2:.R27.R26.Vdd,)P,(6.(7.(28.$12.VR,VHIA,Vh,)(7.R31.A3.R35.R2;.R28.R27.))$62.)P,(6.(7.(29.$12.VR,VHIA,Vh,)(7.R31.A4.R35.R2<.R29.R28.Vdd,))$63.)P,(6.(7.(7.(64.VLB,)+2.)R38.)$65.)P,(=.(6.=R29.)(44.R29.(45.+2.+40.)))P,(24.$9.(47.R2:.+2.)=)P,Ph',(11.$12.VR,VHIA,)PLB',(0.$1.)Pm',P,(13.&40.)(14.(13.&8.))Pd1',$15.Pr,$9.Pt0',(13.&40.)Pt1',(13.&40.)Pt2',(13.&40.)Pa1',(13.&40.)Pa2',(13.&40.)Pa3',(13.&40.)Pa4',(13.&40.)Pa5',(13.&40.)Pa6',(13.&40.)Pa7',(13.&40.)Pt3',(13.&40.)Pt4',(13.&40.)Pt5',(13.&40.)Pt6',(13.&40.)P,(4:.(7.R49.A3.R4=.R43.R40.R3?.)(7.R48.A4.R4<.R43.R40.R3?.Vdd,)R13.R12.R11.R44.R10.R42.R41.)P,A6.R4<.R47.R44.R41.R40.R10.R11.(50.$12.(51.$12.VR,VHIA,R15.Vmo,)R25.(52.(53.(54.&40.R40.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R3<.(54.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R6.R5.R4.R3.)VF,(54.&40.R40.)Vfc,(55.(13.&40.))R13.(56.$12.)))P,(24.(13.&40.)R27.(54.&40.R32.))P,(24.(13.&40.)R27.(54.&40.(37.R2?.)))P,(24.(13.&40.)R27.(54.&40.(37.R2?.)))(50.$12.(51.$12.VR,VHIA,R38.Vmo,)R14.(52.(53.(54.&40.R2?.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R2>.R2=.R2<.Vfpw,R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)VF,(54.&40.R42.)Vfc,(55.(13.&40.))R36.(56.$12.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    intros ENTRY STACK NF C24 PHI FRC Rr HC. intros until Q. intros S SA SB SAB UWA UWB HSTK HNF HPHI HFRC HV HF HC24 HRET HRE K E0 E1 E2. subst xa0 xa1 xa2.
    ddestruct (ep_out v f hk LBk mk A1 d1 A2 d2 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (ep_opnd v f hk LBk mk A1 d1 A2 d2 eA S SA) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM & ANE).
    ddestruct (ep_opnd v f hk LBk mk A1 d1 A2 d2 eB S SB) as (BM & BSEP & BOS & BCR & BCRL & BAO & BIM & BNE).
    pose proof (ep_cnt24 v f hk LBk mk A1 d1 A2 d2 S) as C24k. dpose S as (J & P & S1 & S2 & S12 & U1 & U2).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_binop_stmtA_sz in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (dA := eA) (dB := eB) (lo := lo) (d := dd) (slo := slo);
        rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      - exact HHk.
      - exact HK1.
      - exact HNF.
      - exact XM.
      - exact AM.
      - exact BM.
      - exact ASEP.
      - exact BSEP.
      - exact SAB.
      - exact XNS.
      - intros C; discriminate C.
      - exact AOS.
      - exact BOS.
      - exact ACR.
      - exact ACRL.
      - exact BCR.
      - exact BCRL.
      - exact XWR.
      - exact XLSq.
      - exact STk.
      - exact LOS.
      - clear - SLOK HSTK. lia.
      - intros C; discriminate C.
      - rewrite HTk. clear - TOP FR0. lia.
      - exact SPA.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact XAO.
      - exact AAO.
      - exact BAO.
      - exact AIM.
      - exact BIM.
      - clear - HV HVk. lia.
      - exact (ep_uwc v f hk LBk mk J).
      - rewrite XAD. exact U1.
      - exact UWA.
      - exact UWB.
      - clear - HF HFRk. lia.
      - clear - HC24 C24k. lia.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    eapply (ep_after v f hk LBk mk A1 d1 A2 d2 (PHI d1 eA eB) (FRC d1 eA eB dd) (Rr LBk d1 eA eB) RET); try eassumption.
    all: match goal with |- ?g => idtac "BINOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L12760872139.7 L22358645037.8 L26020610312.10L49959034121.5 L55418262435.9 00000G00j01I01_02<S1R3HIA1h2SP2FR3FR03TOPS1R2SP2lo2FR6STKMAX4SLOK5STACK4HSTKS1R3HIA1h3PHI1v2hk2d12eA2HV3HVkS2LB3C243LBk4HC244C24kS1R3HIA1h2dd3FRC1f2hk2HF4HFRk". (* [comment removed for export] *)
  #[using="IMG EC TPV SP64 SPA SLOK STK0 UW0 XOUW"] Lemma ep_intop : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PENTRY,$9.PSTACK,$9.PNF,$5<.PC24,$9.PPHI,P,$15.P,$15.$9.PFRC,P,$9.$9.PRr,P,(0.$1.)P,$15.P,$15.P,$9.P,$9.P,$15.SpP,(66.$12.VR,VHIA,R7.R6.R5.R4.R3.R2.R1.)Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.PeA,$15.Pb,$9.PRET,$9.Pxt0,(13.&40.)Pxt1,(13.&40.)Pxt2,(13.&40.)Pc1,(13.&40.)Pxa0,(13.&40.)Pxa1,(13.&40.)Pxa2,(13.&40.)Pxa3,(13.&40.)Pxa4,(13.&40.)Pxa5,(13.&40.)Pxa6,(13.&40.)Pxa7,(13.&40.)Pc2,(13.&40.)Pc3,(13.&40.)Pc4,(13.&40.)Pc5,(13.&40.)Pc6,(13.&40.)Pc7,(13.&40.)Pc8,(13.&40.)Pc9,(13.&40.)Pc10,(13.&40.)Pc11,(13.&40.)Pxt3,(13.&40.)Pxt4,(13.&40.)Pxt5,(13.&40.)Pxt6,(13.&40.)PQ,P,$4?.SpP,(4:.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)P,(4>.R23.R22.R20.R1?.)P,(43.VR,(37.R20.)+10.Vdd,)P,(=.(6.(67.(45.+2.+1?.))R20.)(44.R20.(45.+2.+1?.)))P,(6.R32.VSTKMAX,)P,(5?.(60.(61.$1.VLF,)R32.)#200.)P,(6.=A2.R31.R27.R24.)P,(6.=A1.R31.Vdd,)P,(6.(7.(28.$12.VR,VHIA,Vh,)(7.R2?.A2.R33.R29.R26.))$62.)P,(6.(7.(29.$12.VR,VHIA,Vh,)(7.R2?.A1.R33.Vdd,))$63.)P,(6.(7.(7.(64.VLB,)+2.)R36.)$65.)P,(=.(6.=R27.)(44.R27.(45.+2.+40.)))P,(24.$9.(47.R28.+2.)=)P,Ph',(11.$12.VR,VHIA,)PLB',(0.$1.)Pm',P,(13.&40.)(14.(13.&8.))Pd1',$15.Pr,$9.Pt0',(13.&40.)Pt1',(13.&40.)Pt2',(13.&40.)Pa1',(13.&40.)Pa2',(13.&40.)Pa3',(13.&40.)Pa4',(13.&40.)Pa5',(13.&40.)Pa6',(13.&40.)Pa7',(13.&40.)Pt3',(13.&40.)Pt4',(13.&40.)Pt5',(13.&40.)Pt6',(13.&40.)P,(4:.(7.R47.A2.R4;.R41.R3>.)(7.R46.A1.R4:.Vdd,)R13.R12.R11.R42.R10.R40.R3?.)P,A6.R4:.R45.R42.R3?.R3>.R10.R11.(50.$12.(51.$12.VR,VHIA,R15.Vmo,)R23.(52.(53.(54.&40.R3>.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R3:.(54.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R6.R5.R4.R3.)VF,(54.&40.R3>.)Vfc,(55.(13.&40.))R13.(56.$12.)))P,(24.(13.&40.)R25.(54.&40.R30.))P,(24.(13.&40.)R25.(54.&40.(37.R2=.)))P,(24.(13.&40.)R25.(54.&40.R2=.))(50.$12.(51.$12.VR,VHIA,R36.Vmo,)R12.(52.(53.(54.&40.R2=.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R2<.R2;.R2:.Vfpw,R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)VF,(54.&40.R40.)Vfc,(55.(13.&40.))R34.(56.$12.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    intros ENTRY STACK NF C24 PHI FRC Rr HC. intros until Q. intros S SA UWA HB HSTK HNF HPHI HFRC HV HF HC24 HRET HRE K E0 E1 E2. subst xa0 xa1 xa2.
    ddestruct (ep_out v f hk LBk mk A1 d1 A2 d2 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (ep_opnd v f hk LBk mk A1 d1 A2 d2 eA S SA) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM & ANE).
    pose proof (ep_cnt24 v f hk LBk mk A1 d1 A2 d2 S) as C24k. dpose S as (J & P & S1 & S2 & S12 & U1 & U2).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_intop_stmtA_sz in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (dA := eA) (b := b) (lo := lo) (d := dd);
        rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      - exact HHk.
      - exact HK1.
      - exact HNF.
      - exact XM.
      - exact AM.
      - exact ASEP.
      - exact XNS.
      - exact AOS.
      - exact ACR.
      - exact ACRL.
      - exact XWR.
      - exact HB.
      - exact XLSq.
      - exact STk.
      - exact LOS.
      - clear - SLOK HSTK. lia.
      - rewrite HTk. clear - TOP FR0. lia.
      - exact SPA.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact XAO.
      - exact AAO.
      - exact AIM.
      - clear - HV HVk. lia.
      - exact (ep_uwc v f hk LBk mk J).
      - rewrite XAD. exact U1.
      - exact UWA.
      - clear - HF HFRk. lia.
      - clear - HC24 C24k. lia.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    eapply (ep_after v f hk LBk mk A1 d1 A2 d2 (PHI d1 eA) (FRC dd) (Rr LBk d1 eA b) RET); try eassumption.
    all: match goal with |- ?g => idtac "INTOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L12760872139.7 L17320213766.11L22358645037.8 L26498980917.10L49959034121.5 00000G00i01L01j02@S1R3HIA1h2SP2FR3FR03TOPS1R3HIA1h2dd1f2hk2eA2eE2eN2HF4HFRkS1R2SP2lo2FR6STKMAX4SLOK5STACK4HSTKS1R3HIA1h1v2hk2eA2eE2eN2HV3HVkS2LB3C243LBk4HC244C24k". (* [comment removed for export] *)
  #[using="IMG EC slo TPV SP64 SPA SLOK STK0 UW0 XOUW SSH SLO1 SLO3"] Lemma ep_expmod : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PENTRY,$9.PSTACK,$9.PNF,$5<.PC24,$9.P,(68.$12.VR,VHIA,R4.R3.R2.R1.)Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.PeA,$15.PeE,$15.PeN,$15.PRET,$9.Pxt0,(13.&40.)Pxt1,(13.&40.)Pxt2,(13.&40.)Pc1,(13.&40.)Pxa0,(13.&40.)Pxa1,(13.&40.)Pxa2,(13.&40.)Pxa3,(13.&40.)Pxa4,(13.&40.)Pxa5,(13.&40.)Pxa6,(13.&40.)Pxa7,(13.&40.)Pc2,(13.&40.)Pc3,(13.&40.)Pc4,(13.&40.)Pc5,(13.&40.)Pc6,(13.&40.)Pc7,(13.&40.)Pc8,(13.&40.)Pc9,(13.&40.)Pc10,(13.&40.)Pc11,(13.&40.)Pxt3,(13.&40.)Pxt4,(13.&40.)Pxt5,(13.&40.)Pxt6,(13.&40.)PQ,P,$4?.SpP,(4:.R28.R27.R26.R25.R24.R23.R22.R21.R20.)P,(4>.R24.R23.R21.R20.)P,(4>.R25.R24.R22.R20.)P,(4>.R26.R25.R23.R20.)P,(3;.(24.$15.R22.R26.))P,(3;.(24.$15.R22.R27.))P,(6.(35.R23.)+1387.)P,(6.(35.R29.)(35.R26.))P,(43.VR,(37.R27.)+10.Vdd,)P,(43.VR,(37.R27.)+10.Vdd,)P,(43.VR,(37.R27.)+10.Vdd,)P,(6.R37.VSTKMAX,)P,(5?.(60.(61.$1.VLF,)R37.)#200.)P,(6.=(69.(35.R2<.)(35.R2;.)(35.R2:.)))P,(6.=(6:.(35.R2=.)(35.R2<.)(35.R2;.)Vdd,))P,(6.(7.(28.$12.VR,VHIA,Vh,)(7.R37.(69.(35.R2>.)(35.R2=.)(35.R2<.))))$62.)P,(6.(7.(29.$12.VR,VHIA,Vh,)(7.R37.(6:.(35.R2?.)(35.R2>.)(35.R2=.)Vdd,)))$63.)P,(6.(7.(7.(64.VLB,)+2.)R3;.)$65.)P,(=.(6.=R2>.)(44.R2>.(45.+2.+40.)))P,(24.$9.(47.R2?.+2.)=)P,Ph',(11.$12.VR,VHIA,)PLB',(0.$1.)Pm',P,(13.&40.)(14.(13.&8.))Pd1',$15.Pr,$9.Pt0',(13.&40.)Pt1',(13.&40.)Pt2',(13.&40.)Pa1',(13.&40.)Pa2',(13.&40.)Pa3',(13.&40.)Pa4',(13.&40.)Pa5',(13.&40.)Pa6',(13.&40.)Pa7',(13.&40.)Pt3',(13.&40.)Pt4',(13.&40.)Pt5',(13.&40.)Pt6',(13.&40.)P,(4:.(7.R4?.(69.(35.R46.)(35.R45.)(35.R44.)))(7.R4>.(6:.(35.R46.)(35.R45.)(35.R44.)Vdd,))R13.R12.R11.R4:.R10.R48.R47.)P,(6;.R4=.R4:.R47.R46.R45.R10.R11.)(50.$12.(51.$12.VR,VHIA,R15.Vmo,)R2:.(52.(53.(54.&40.R45.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R41.(54.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R6.R5.R4.R3.)VF,(54.&40.R45.)Vfc,(55.(13.&40.))R13.(56.$12.)))P,(24.(13.&40.)R2<.(54.&40.R38.))P,(24.(13.&40.)R2<.(54.&40.(37.R35.)))P,(24.(13.&40.)R2<.(54.&40.(37.R35.)))P,(24.(13.&40.)R2<.(54.&40.(37.R35.)))P,(24.(13.&40.)R2<.(54.&40.=))(50.$12.(51.$12.VR,VHIA,R40.Vmo,)R1;.(52.(53.(54.&40.R36.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R35.R34.R33.Vfpw,R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)VF,(54.&40.R47.)Vfc,(55.(13.&40.))R3>.(56.$12.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    intros ENTRY STACK NF C24 HC. intros until Q. intros S SA SE SN NEE NEN N4999 NXA UWA UWE UWN HSTK HNF HPHI HFRC HV HF HC24 HRET HRE K E0 E1 E2 E3 E4. subst xa0 xa1 xa2 xa3 xa4.
    ddestruct (ep_out v f hk LBk mk A1 d1 A2 d2 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (ep_opnd v f hk LBk mk A1 d1 A2 d2 eA S SA) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM & ANE).
    ddestruct (ep_opnd v f hk LBk mk A1 d1 A2 d2 eE S SE) as (EM & ESEP & EOS & ECR & ECRL & EAO & EIM & ENE).
    ddestruct (ep_opnd v f hk LBk mk A1 d1 A2 d2 eN S SN) as (NM & NSEP & NOS & NCR & NCRL & NAO & NIM & NNE).
    pose proof (ep_cnt24 v f hk LBk mk A1 d1 A2 d2 S) as C24k. dpose S as (J & P & S1 & S2 & S12 & U1 & U2).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (ENE' : md_addr d1 <> md_addr eE) by (destruct ENE as [C|C]; [exfalso; exact (NEE C)| exact C]).
    assert (NNE' : md_addr d1 <> md_addr eN) by (destruct NNE as [C|C]; [exfalso; exact (NEN C)| exact C]).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_exp_mod_stmtA_sz in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (dA := eA) (dE := eE) (dN := eN) (lo := lo) (d := dd) (slo := slo);
        rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      - exact HHk.
      - exact HK1.
      - exact HNF.
      - exact XM.
      - exact AM.
      - exact EM.
      - exact NM.
      - exact N4999.
      - exact NXA.
      - exact ASEP.
      - exact ESEP.
      - exact NSEP.
      - exact ENE'.
      - exact NNE'.
      - exact XNS.
      - exact AOS.
      - exact EOS.
      - exact NOS.
      - exact ACR.
      - exact ACRL.
      - exact ECR.
      - exact ECRL.
      - exact NCR.
      - exact NCRL.
      - exact XWR.
      - exact XLSq.
      - exact STk.
      - exact LOS.
      - clear - SLOK HSTK. lia.
      - exact (ep_sshad v f hk LBk mk J).
      - exact SLO1.
      - exact SLO3.
      - rewrite HTk. clear - TOP FR0. lia.
      - exact SPA.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact XAO.
      - exact AAO.
      - exact EAO.
      - exact NAO.
      - exact AIM.
      - exact EIM.
      - exact NIM.
      - clear - HV HVk. lia.
      - exact (ep_uwc v f hk LBk mk J).
      - rewrite XAD. exact U1.
      - exact UWA.
      - exact UWE.
      - exact UWN.
      - clear - HF HFRk. lia.
      - clear - HC24 C24k. lia.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity. }
    eapply (ep_after v f hk LBk mk A1 d1 A2 d2 _ _ (exp_mod_Rsz LBk d1 eA eE eN) RET); try eassumption.
    all: match goal with |- ?g => idtac "EXPMOD-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L13047154303.9 L13311483896.23L15756354262.4 L28776808227.3 L33296804446.2 L38948636245.0 L4295316307.26 L46798920039.7 L49595303303.3 L49815258316.3 L52320020432.3 L54303607689.9 L59657045483.12L6412581986.8  L9689407360.2  00000U00V00d00o01601701801M01X01a01j02M03803T03[S1R2SP2lo2FR6STKMAX4STK03LOS3FR04LOSPFS1R2lo3LOS3ALOS2A12A23S12S2SP2FRSFS2SP2lo2FR3SLO2A13SL1S2MC2A23MS2S2MC1x2K2S2A12dZ1KS2SP2lo2FR2MC6STKMAX4STK04LOSP4MCLOS1R3HIA1h2SP2lo2FR6STKMAX4STK03FR04LOSP1a1SS1R2MC3DI13DI23MC13MC22dZ2BIS2dZ2N1". (* [comment removed for export] *)
  #[using="EC STKMAX SP64 SPA SLOK STK0"] Lemma epair_call_mc : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.Pm',P,(13.&40.)(14.(13.&8.))Ph',(11.$12.VR,VHIA,)PLB',(0.$1.)Pd1',$15.Pdv,$9.Pdf,$9.P,(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R?.R>.R=.R<.R;.)P,(42.VR,VHIA,VLB,VLF,R>.R=.R<.R;.R:.R9.R8.)P,(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,R<.)P,(18.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,R;.)P,(5.(6.(7.R>.+10.)R<.)(6.(7.R<.+10.)R>.))P,(6.=R7.)P,(6.=R7.)P,(1:.$12.R=.)P,(1;.$12.R>.Vlo,(19.VSP,VFR,))P,(1<.$12.VR,(1=.R15.R12.)VLF,(19.VSP,VFR,)(1>.VR,)(1?.$12.VR,VHIA,R16.)(20.(21.$9.$9.)(22.$9.$9.R13.(7.R13.+10.))(20.(21.$9.$9.)(22.$9.$9.VMC,(7.VMC,+8.))(23.(21.$9.$9.))))R14.R?.)P,(24.$9.(25.$12.VR,VHIA,R?.)(25.$12.VR,VHIA,R17.))P,(24.$9.(1?.$12.VR,VHIA,R10.)(1?.$12.VR,VHIA,R18.))P,(24.$9.(26.$12.VR,VHIA,R11.)(26.$12.VR,VHIA,R19.))P,Px,$9.P,(27.$12.VR,VHIA,R1;.R1.)(27.$12.VR,VHIA,R14.R2.)P,(6.(28.$12.VR,VHIA,R13.)(7.(28.$12.VR,VHIA,R1;.)R10.))P,(6.(29.$12.VR,VHIA,R14.)(7.(29.$12.VR,VHIA,R1<.)R10.))P,(2:.$12.VR,VHIA,R15.R14.VLF,R16.)P,(2;.$12.R17.R15.R14.)P,(2<.R1>.R1;.R16.R15.)P,Pb,$1.P,(4.$1.R1.(10.R17.))(5.(4.$1.R2.(10.R1>.))(2=.VR,(1=.R21.R1>.)VLF,(8.$9.$9.R2.)(:.$9.$9.R2.)))P,(<.(13.&40.)Lc,(13.&40.)(6<.$12.R1;.VMC,(20.$6=.(6>.R1.)(23.$6=.))))(=.(16.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,(7.R24.R17.)(7.R23.R16.)R1:.R19.R1;.)(42.VR,VHIA,VLB,VLF,R1:.R19.R1;.R1?.R18.R1=.R1<.))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    intros until df. (intros J dd_H; ddestruct dd_H as (T1 & T2 & D12 & COV); intros dd_H; ddestruct dd_H as (CW1 & SL1 & XI1 & MS1); intros dd_H; ddestruct dd_H as (CW2 & SL2 & _ & MS2); intros S12 Hdv Hdf MI' ST' HP HT' HS' HF' HCS' HV' HFR' HH' M1' OUT' FRA' MC').
    assert (HSP2 : arl_stklo R <= SP - FR <= SP) by (clear - LOS LOSP STK0 FR0; lia).
    assert (CRA : forall A, client_wrange L (LB ++ fdata LF) SP (htop asegs R HIA h) A 16 -> client_range L (LB ++ fdata LF) lo A 16).
    { intros A CW a Ha. destruct (CW a Ha) as [S|[D|Bk]]; [left; clear - S LOSP STK0 FR0; lia| right; left; exact D| right; right; exact Bk]. }
    ddestruct MCOK as (MC1 & MC2 & _).
    assert (LAP : forall A dZ, TMP hk LBk mk A dZ -> md_own dZ = LHeap -> disjoint_from [(A1, A1 + 16); (MC, MC + 8)] (md_p dZ) (4 * md_n dZ)).
    { intros A dZ TZ EO. ddestruct (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A dZ J TZ EO) as (_ & N1 & _ & _ & BI & _ & FRA).
      destruct (fresh_apart_client R LB LF lo A1 16 _ _ FRA (CRA A1 CW1) ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K|K];
        cbn [disjoint_from fst snd]; (split; [clear - K; lia| split; [destruct DIMG as [DI1 DI2]; clear - BI MC1 MC2 DI1 DI2; lia| exact I]]). }
    pose proof (ej_aobj_call R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 m' h' (SP - FR) _ J T1 CW1 HSP2 HP HCS') as OA1'.
    destruct (ej_call R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 m' h' LB' d1' (SP - FR) dv df [(A1, A1 + 16); (MC, MC + 8)] J T1
                ltac:(clear; lia) Hdv Hdf MI' ST' HP) as [J' T1'];
      first [ assumption | solve [intros x Hx; pose proof (XI1 x Hx) as K1; pose proof (XOMC x Hx) as K2; cbn [outside fst snd] in *; split; [exact (proj1 K1)| split; [clear - K2; lia| exact I]]]
            | solve [cbn [disjoint_from fst snd]; split; [clear - SL1 FR0 SLO; lia| split; [clear - MCLO LOSP STK0 FR0; lia| exact I]]] | solve [clear - LOSP STK0; lia] | idtac ].
    destruct (ejtmp_keep R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 A2 d2 m' h' LB' d1' (SP - FR) _ J T1 T2 D12 CW2 HSP2 HP
                ltac:(cbn [disjoint_from fst snd]; split; [clear - S12; lia| split; [clear - MS2; lia| exact I]]) (LAP A2 d2 T2) MI' HCS' OUT' M1' FRA') as [T2' D12'].
    split; [exact J'|]. refine (conj T1' (conj T2' (conj D12' _))).
    dpose OUT' as (_ & _ & O3 & _ & O5).
    intros b Hb. destruct (O3 b Hb) as [K1|K1]; [| right; apply in_or_app; left; exact K1].
    destruct (COV b K1) as [K2|K2]; [left; exact K2| right]. rewrite !in_app_iff in *. destruct K2 as [K2|K2]; [left; rewrite (O5 b K2 Hb); exact K2| right; exact K2].
    all: match goal with |- ?g => idtac "PAIRMC-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (G : Z) (g : ecp_grp).
  Hypothesis GRP : ecp_grp_preA asegs R HIA MT h LB LF m G g MC lo SP dd.
  Hypothesis DXG : disjoint_from XO G 192.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L10678603361.3 L12760872139.7 L19715409235.9 L19725894707.8 L19725895507.10L19726054483.4 L20576254252.7 L23725798599.11L23736092103.7 L23736284583.10L23736284871.12L57853566577.8 L57859858193.10L59109473202.9 L59119958450.9 L59119958738.1100000;00R00S00T00U00g01D01E01F01G01H01_01`01a02<02=S2SP2FR3FR0S1R3HIA1h2SP2FR3FR03TOPFFFS2LB3LBk4HC244C24kS1R2SP2lo2FR6STKMAX4SLOK4HSTKFFFFS1R3HIA1h1v2hk1N2HV3HVkFFS1R3HIA1h2dd1f2hk1N2HF4HFRkF". (* [comment removed for export] *)
  #[using="IMG EC slo TPV SP64 SPA SLOK STK0 UW0 XOUW SSH SLO1 SLO3 GRP DXG"] Lemma ep_rhs : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PENTRY,$9.P,(6?.$12.VR,VHIA,VMT,R1.VMC,)Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.PeA,$15.PN,$9.PRET,$9.Pxt0,(13.&40.)Pxt1,(13.&40.)Pxt2,(13.&40.)Pc1,(13.&40.)Pxa0,(13.&40.)Pxa1,(13.&40.)Pxa2,(13.&40.)Pxa3,(13.&40.)Pxa4,(13.&40.)Pxa5,(13.&40.)Pxa6,(13.&40.)Pxa7,(13.&40.)Pc2,(13.&40.)Pc3,(13.&40.)Pc4,(13.&40.)Pc5,(13.&40.)Pc6,(13.&40.)Pc7,(13.&40.)Pc8,(13.&40.)Pc9,(13.&40.)Pc10,(13.&40.)Pc11,(13.&40.)Pxt3,(13.&40.)Pxt4,(13.&40.)Pxt5,(13.&40.)Pxt6,(13.&40.)PQ,P,$4?.SpP,(4:.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)P,(70.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VXO,R23.R1?.)P,(43.VR,(37.R20.)+10.Vdd,)P,(5.(6.(7.VMC,+8.)(37.R21.))(6.(7.(37.R21.)+10.)VMC,))P,(5.(6.(7.R26.+10.)VG,)(6.(7.VG,+<0.)R26.))P,(24.$30.(31.R26.)$4=.)P,(24.$9.(38.(71.Vg,))+1.)P,(24.$9.(38.(72.Vg,))+1.)P,(6.+1.(73.(74.Vg,)))P,(75.Vg,R26.)P,(6.(35.R28.)R27.)P,(6.+450.VSTKMAX,)P,(5?.(60.(61.$1.VLF,)#2.)#200.)P,(6.=(76.R2:.))P,(6.=(77.R2;.Vdd,))P,(6.(7.(28.$12.VR,VHIA,Vh,)(7.R36.(76.R2<.)))$62.)P,(6.(7.(29.$12.VR,VHIA,Vh,)(7.R36.(77.R2=.Vdd,)))$63.)P,(6.(7.(7.(64.VLB,)+2.)$78.)$65.)P,(=.(6.=R2>.)(44.R2>.(45.+2.+40.)))P,(24.$9.(47.R2?.+2.)=)P,Ph',(11.$12.VR,VHIA,)PLB',(0.$1.)Pm',P,(13.&40.)(14.(13.&8.))Pd1',$15.Pr,$9.Pt0',(13.&40.)Pt1',(13.&40.)Pt2',(13.&40.)Pa1',(13.&40.)Pa2',(13.&40.)Pa3',(13.&40.)Pa4',(13.&40.)Pa5',(13.&40.)Pa6',(13.&40.)Pa7',(13.&40.)Pt3',(13.&40.)Pt4',(13.&40.)Pt5',(13.&40.)Pt6',(13.&40.)P,(4:.(7.R4>.(76.R44.))(7.R4=.(77.R44.Vdd,))R13.R12.R11.R49.R10.R47.R46.)P,(79.R4<.R49.R10.R11.)P,(6.(35.R12.)(7:.R46.))(50.$12.(51.$12.VR,VHIA,R16.Vmo,)R2;.(52.(53.(54.&40.R46.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R11.R10.R?.Vfpw,R42.(54.&40.R12.)R>.R=.R<.R;.R:.R9.R8.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R7.R6.R5.R4.)VF,(54.&40.R46.)Vfc,(55.(13.&40.))R14.(56.$12.)))P,(24.(13.&40.)R2<.(54.&40.VG,))P,(24.(13.&40.)R2<.(54.&40.R38.))P,(24.(13.&40.)R2<.(54.&40.(37.R35.)))(50.$12.(51.$12.VR,VHIA,R3=.Vmo,)R19.(52.(53.(54.&40.R34.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R33.R32.R31.Vfpw,R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)VF,(54.&40.R41.)Vfc,(55.(13.&40.))R3;.(56.$12.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    intros ENTRY HC. intros until Q. intros S EXA UWA AMC AG EO SGA SGB VP NLE NAN HSTK HNF HPHI HFRC HV HF HC24 HRET HRE K E0 E1 E2. subst xa0 xa1 xa2.
    ddestruct (ep_out v f hk LBk mk A1 d1 A2 d2 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (ep_opnd v f hk LBk mk A1 d1 A2 d2 eA S (or_intror (or_intror EXA))) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM & ANE).
    pose proof (ep_cnt24 v f hk LBk mk A1 d1 A2 d2 S) as C24k. dpose S as (J & P & S1 & S2 & S12 & U1 & U2).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk [ck MCk] STk FRk].
    pose proof (ej_grp_pre R HIA h LB LF m SP lo FR FRAME XO MC EC MT v f hk LBk mk G g (SP - FR) dd J GRP DXG ltac:(clear - FR0; lia)) as GRPk.
    assert (EXT : ext_opndA asegs R HIA hk LBk LF mk d1 eA MC (SP - FR) lo dd).
    { unfold ext_opndA. split; [exact AM|]. split; [rewrite XAD; ddestruct EXA as (_ & _ & _ & _ & _ & _ & K7 & _); exact K7|].
      split; [exact AOS|]. split; [exact ACR|]. split; [exact ACRL|]. split; [exact AMC|]. split; [exact AAO|]. split; [exact AIM| exact UWA]. }
    assert (OSk : ecp_out_sepA d1 G MC).
    { unfold ecp_out_sepA. rewrite XAD. split; [exact AG|]. split; [intros C; rewrite EO in C; discriminate C|]. ddestruct S1 as (_ & _ & _ & MS1). exact MS1. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold ecp_sw_rhs_stmtA, ecp_rhs_stmtA in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (dA := eA) (G := G) (g := g) (cnt := ck) (N := N) (lo := lo) (d := dd) (slo := slo); cbv iota;
        rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      all: first [ exact HHk | exact HK1 | exact HNF | exact GRPk | exact OSk | exact SGA | exact SGB | exact VP | (intros C; discriminate C) | exact NLE | exact NAN
                 | exact XM | exact EO | exact XWR | exact EXT | exact MCk | exact MCOK | exact LOS | exact (ep_sshad v f hk LBk mk J) | exact SLO1 | exact SLO3 | exact SPA | exact TPV | exact MIk
                 | exact XAO | exact (ep_uwc v f hk LBk mk J) | (rewrite XAD; exact U1) | reflexivity | exact STk
                 | (rewrite unsigned_lit by exact HRET; exact HRE)
                 | (rewrite HTk; clear - TOP FR0; lia) | (clear - SLOK HSTK; lia) | (clear - HV HVk; lia) | (clear - HF HFRk; lia)
                 | (clear - HC24 C24k; lia)
                 | (rewrite XAD; split; reflexivity) | idtac ].
      all: match goal with |- ?g => idtac "RHS-PRE-LEFT:" g end. }
    cbv iota. (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold ecp_mul_mod_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dY2 & r & cnt2 & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MY2 & OUT2 & FRA2 & GR2 & MCC2 & MR2 & SZ2).
    injection E as E1 E2. subst ms' mo'. rewrite XAD in HP2.
    rewrite ?(unsigned_lit (SP - FR)) in ST2, HP2 by exact SPR.
    rewrite (ret_pc_even RET HRET HRE).
    destruct (epair_call_mc v f hk LBk mk A1 d1 A2 d2 m2 h2 LB2 dY2 (sw_rhs_PHIn N) (sw_rhs_FRn N dd)
                J P S1 S2 S12 HPHI HFRC MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MY2 OUT2 FRA2 ltac:(exists cnt2; exact MCC2)) as [J2 P2].
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [| exact MR2| exact SZ2].
    exact (conj J2 (conj P2 (conj S1 (conj S2 (conj S12 (conj U1 U2)))))).
    all: match goal with |- ?g => idtac "RHS-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L2333536794.11L33296804446.2L38235734261.100000S00Z00^S1R3HIA1h2SP2lo2FR3LOS3FR03TOP1a2HaS2SP2FRS2lo". (* [comment removed for export] *)
  #[using="EC"] Lemma ep_scratch : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.Pm',P,(13.&40.)(14.(13.&8.))P,(4:.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(2>.(20.(21.$9.$9.)(22.$9.$9.Vlo,(19.VSP,VFR,))(23.(21.$9.$9.)))R7.R2.)P,(2?.$12.R8.R3.)P,(1:.$12.R4.)P,(1;.$12.R5.Vlo,(19.VSP,VFR,))(4:.R?.R>.R=.R<.R6.R:.R9.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    ec_open. (intros v f hk LBk mk A1 d1 A2 d2 m' dd_H; ddestruct dd_H as (J & P & S1 & S2 & S12 & U1 & U2); intros MU WM MI' ST').
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (HH' : HM asegs R HIA hk LBk LF m').
    { eapply (hm_munch asegs R HIA hk LBk LF [(lo, SP - FR)] mk m' HHk MU WM).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite HTk. clear - Ha LOS TOP FR0. lia. }
    destruct (epair_scratch R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 A2 d2 lo (SP - FR) m' J P S1 S2 MU WM MI' ST' HH' ltac:(clear; lia) ltac:(clear; lia)) as [J' P'].
    exact (conj J' (conj P' (conj S1 (conj S2 (conj S12 (conj U1 U2)))))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L35653327737.8L54395982181.7L59308660947.3L60098763854.3L61352325225.600000K00l01601@01US1R3HIA1h2SP2lo2FR3FR04SPHIS2SP2lo2FR6STKMAX4LOSP5STACK4HSTKS2d12N12E0S1R2lo3LOSS2SP2lo2FR3FR02A13SL1". (* [comment removed for export] *)
  #[using="EC SP64 SPA SLOK STK0"] Lemma ep_query : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PENTRY,$9.PSTACK,$9.PPRE,P,$15.P,$9.SpPRq,P,$15.P,$9.P,$9.SpP,(7;.$12.(40.VR,)R4.R3.R2.R1.)Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.Pz,$9.PRET,$9.Pxt0,(13.&40.)Pxt1,(13.&40.)Pxt2,(13.&40.)Pc1,(13.&40.)Pxa0,(13.&40.)Pxa1,(13.&40.)Pxa2,(13.&40.)Pxa3,(13.&40.)Pxa4,(13.&40.)Pxa5,(13.&40.)Pxa6,(13.&40.)Pxa7,(13.&40.)Pc2,(13.&40.)Pc3,(13.&40.)Pc4,(13.&40.)Pc5,(13.&40.)Pc6,(13.&40.)Pc7,(13.&40.)Pc8,(13.&40.)Pc9,(13.&40.)Pc10,(13.&40.)Pc11,(13.&40.)Pxt3,(13.&40.)Pxt4,(13.&40.)Pxt5,(13.&40.)Pxt6,(13.&40.)PQ,P,$4?.SpP,(4:.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)P,A2.R2:.R21.R1>.P,(6.R2<.VSTKMAX,)P,(=.(6.=R1?.)(44.R1?.(45.+2.+40.)))P,(24.$9.(47.R20.+2.)=)P,Pm',P,(13.&40.)(14.(13.&8.))Pr,$9.Pt0',(13.&40.)Pt1',(13.&40.)Pt2',(13.&40.)Pa1',(13.&40.)Pa2',(13.&40.)Pa3',(13.&40.)Pa4',(13.&40.)Pa5',(13.&40.)Pa6',(13.&40.)Pa7',(13.&40.)Pt3',(13.&40.)Pt4',(13.&40.)Pt5',(13.&40.)Pt6',(13.&40.)P,(4:.R3;.R3:.R39.R38.R10.R36.R35.R34.R33.)P,A3.R3>.R36.R33.R10.(50.$12.(51.$12.VR,VHIA,R3;.Vmo,)R18.(52.(53.(54.&40.R33.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R2?.(54.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R6.R5.R4.R3.)VF,(54.&40.R33.)Vfc,(55.(13.&40.))R12.(56.$12.)))P,(24.(13.&40.)R1=.(54.&40.R27.))P,(24.(13.&40.)R1=.(54.&40.R24.))(50.$12.(51.$12.VR,VHIA,R2<.Vmo,)R9.(52.(53.(54.&40.R24.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R23.R22.R21.Vfpw,R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)VF,(54.&40.R33.)Vfc,(55.(13.&40.))R2:.(56.$12.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    intros ENTRY STACK PRE Rq HQ. intros until Q. intros S HPRE HSTK HRET HRE K E0 E1. subst xa0 xa1.
    ddestruct (ep_out v f hk LBk mk A1 d1 A2 d2 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    dpose S as (J & (T1 & _) & (_ & SL1 & _) & _). pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (SCS : crange (hcs asegs R HIA hk) lo (SP - FR - lo)).
    { eapply crange_sub; [exact (hcs_stack asegs R HIA hk)| clear - LOS; lia| rewrite HSk; clear - SPHI FR0; lia]. }
    assert (XNL : 1 <= md_n d1 -> md_own d1 = LHeap).
    { intros N1. pose proof XM as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own d1); [exfalso; destruct OW as [_ E0]; clear - E0 N1; lia| reflexivity| exfalso; exact (XNS eq_refl)]. }
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo).
    { unfold mpi_query_stmtA in HQ.
      eapply HQ with (CS := hcs asegs R HIA hk) (LB := LBk) (dX := d1) (v := z) (lo := lo); rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      - exact XM.
      - intros EO. ddestruct (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 J T1 EO) as (_ & _ & P0 & _). exact P0.
      - exact MIk.
      - exact HPRE.
      - exact (art_alwf asegs R HIA).
      - exact (hcs_ok asegs R HIA hk).
      - exact (hm_abase asegs R HIA hk LBk LF mk HHk).
      - exact (proj1 XAO).
      - intros N1. pose proof (XNL N1) as EO. destruct (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 J T1 EO) as (IN & _).
        eapply hm_aobj_block; [exact HHk| exact IN].
      - exact STk.
      - exact LO0.
      - clear - LOSP HSTK. lia.
      - exact SPA.
      - exact SCS.
      - rewrite XAD. clear - SL1 FR0. lia.
      - intros N1. apply XLSq. rewrite (XNL N1). discriminate.
      - rewrite XAD. reflexivity.
      - reflexivity. }
    intros ms' PO. unfold mpi_query_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & r & E & MU2 & WM2 & MI2 & ST2 & RR). subst ms'.
    rewrite ?(unsigned_lit (SP - FR)) in MU2, ST2 by exact SPR.
    rewrite (ret_pc_even RET HRET HRE).
    eapply K; [| exact RR]. exact (ep_scratch v f hk LBk mk A1 d1 A2 d2 m2 S MU2 WM2 MI2 ST2).
    all: match goal with |- ?g => idtac "QUERY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L12760872139.7L18073002003.1L33306266156.9L34303954862.4L40402727500.6L59308585216.4L61352325225.6L8681788683.1 00000G00K01001:01N01[020024S1R3HIA1h2SP2FR3FR03TOPS2d1S1R2SP2lo2FR6STKMAX4SLOK3NRA3NER4HSTKS2d11x3N0'S1R2lo3LOS3ALO2d12B2S2d13N0'1a2HaS2SP2lo2FR3FR02A13SL1S2d1". (* [comment removed for export] *)
  #[using="EC SP64 SPA SLOK STK0"] Lemma ep_shift_r : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PENTRY,$9.P,(7<.$12.VR,VHIA,R1.)Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.Pcount,$9.PRET,$9.Pxt0,(13.&40.)Pxt1,(13.&40.)Pxt2,(13.&40.)Pc1,(13.&40.)Pxa0,(13.&40.)Pxa1,(13.&40.)Pxa2,(13.&40.)Pxa3,(13.&40.)Pxa4,(13.&40.)Pxa5,(13.&40.)Pxa6,(13.&40.)Pxa7,(13.&40.)Pc2,(13.&40.)Pc3,(13.&40.)Pc4,(13.&40.)Pc5,(13.&40.)Pc6,(13.&40.)Pc7,(13.&40.)Pc8,(13.&40.)Pc9,(13.&40.)Pc10,(13.&40.)Pc11,(13.&40.)Pxt3,(13.&40.)Pxt4,(13.&40.)Pxt5,(13.&40.)Pxt6,(13.&40.)PQ,P,$4?.SpP,(4:.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)P,(=.(6.=R1>.)(44.R1>.(45.+2.+40.)))P,(6.+40.VSTKMAX,)P,(=.(6.=R1?.)(44.R1?.(45.+2.+40.)))P,(24.$9.(47.R20.+2.)=)P,Pm',P,(13.&40.)(14.(13.&8.))Pd1',$15.Pt0',(13.&40.)Pt1',(13.&40.)Pt2',(13.&40.)Pa1',(13.&40.)Pa2',(13.&40.)Pa3',(13.&40.)Pa4',(13.&40.)Pa5',(13.&40.)Pa6',(13.&40.)Pa7',(13.&40.)Pt3',(13.&40.)Pt4',(13.&40.)Pt5',(13.&40.)Pt6',(13.&40.)P,(4:.R3;.R3:.R39.R38.R10.R36.R?.R34.R33.)P,(24.$9.(35.R10.)(35.R36.))P,(24.$30.(31.R11.)(31.R37.))(50.$12.(51.$12.VR,VHIA,R3<.Vmo,)R19.(52.(53.(54.&40.R34.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R11.R10.R?.Vfpw,R30.(54.&40.=)R>.R=.R<.R;.R:.R9.R8.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R7.R6.R5.R4.)VF,(54.&40.R34.)Vfc,(55.(13.&40.))R13.(56.$12.)))P,(24.(13.&40.)R1=.(54.&40.R27.))P,(24.(13.&40.)R1=.(54.&40.R24.))(50.$12.(51.$12.VR,VHIA,R2<.Vmo,)R9.(52.(53.(54.&40.R24.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R23.R22.R21.Vfpw,R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)VF,(54.&40.R30.)Vfc,(55.(13.&40.))R2:.(56.$12.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    pose proof (arl_need_rt_amem R) as NRA. pose proof (arl_need_ecp_rt R) as NER.
    intros ENTRY HSR. intros until Q. intros S HCNT HSTK HRET HRE K E0 E1. subst xa0 xa1.
    ddestruct (ep_out v f hk LBk mk A1 d1 A2 d2 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    dpose S as (J & P & S1 & S2 & S12 & U1 & U2). pose proof P as (T1 & _). dpose S1 as (_ & SL1 & _).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    pose proof (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 J T1) as BLK.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo).
    { unfold mpi_shift_r_stmtA in HSR.
      eapply HSR with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (count := count) (lo := lo); rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      - exact HHk.
      - exact XM.
      - exact XNS.
      - intros EO. ddestruct (BLK EO) as (_ & _ & _ & B2 & _). clear - B2 ALO LOS. lia.
      - exact MIk.
      - exact HCNT.
      - exact STk.
      - exact LOS.
      - clear - SLOK HSTK NRA NER. lia.
      - rewrite HTk. clear - TOP FR0. lia.
      - exact SPA.
      - rewrite XAD. clear - SL1 FR0. lia.
      - intros EO. exact (proj1 (proj2 XOS) EO).
      - destruct (md_own d1) eqn:EO.
        + pose proof XM as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. destruct OW as [_ N0']. intros a Ha. exfalso. clear - Ha N0'. lia.
        + destruct (BLK eq_refl) as (IN & _). eapply client_wrange_block; [apply in_or_app; left; exact IN| clear; lia| clear; lia].
        + exfalso. exact (XNS eq_refl).
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact (proj1 XAO).
      - rewrite XAD. reflexivity.
      - reflexivity. }
    intros ms' PO. unfold mpi_shift_r_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & xs' & E & MU2 & WM2 & MI2 & ST2 & MX2 & LEN2 & _ & HH2). subst ms'.
    rewrite ?(unsigned_lit (SP - FR)) in MU2, ST2 by exact SPR.
    rewrite (ret_pc_even RET HRET HRE).
    destruct (md_own d1) eqn:EO.
    - (* [comment removed for export] *)
      assert (MU2' : munch [(lo, SP - FR)] mk m2).
      { intros x Hx. apply MU2. cbn [outside fst snd] in *. pose proof XM as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. destruct OW as [P0' N0'].
        split; [exact (proj1 Hx)|]. split; [clear - P0' N0'; lia| exact I]. }
      eapply (K m2 d1); [exact (ep_scratch v f hk LBk mk A1 d1 A2 d2 m2 S MU2' WM2 MI2 ST2)| reflexivity| exact EO].
    - destruct (epair_limbs R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 A2 d2 m2 xs' J P S1 S2 EO MU2 WM2 MI2 ST2 ltac:(rewrite EO; exact MX2)) as [J' P'].
      eapply K; [exact (conj J' (conj P' (conj S1 (conj S2 (conj S12 (conj U1 U2))))))| reflexivity| cbn [md_own]; exact EO].
    - exfalso. exact (XNS eq_refl).
    all: match goal with |- ?g => idtac "SHIFTR-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L1099663187.4 L1099663187.8 L60289852366.500000:00Q00`S2dq1B1j1KS2dq1B1j3FBq2nq2H12H21KS1R2D12D22dq2BI". (* [comment removed for export] *)
  #[using="h LB m SP lo FR FRAME XO MC EC"] Lemma ep_keep_fresh : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Phq,(11.$12.VR,VHIA,)PLBq,(0.$1.)Pmq,P,(13.&40.)(14.(13.&8.))Pdq,$15.P,(2:.$12.VR,VHIA,R4.R3.VLF,R2.)P,(24.$30.(31.R2.)$32.)P,(4.(21.$9.$9.)(22.$9.$9.(33.R3.)(34.+4.(35.R3.)))R5.)(2=.VR,(1=.R6.R4.)VLF,(33.R4.)(34.+4.(35.R4.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. intros hq LBq mq dq HHq EO XIN. pose proof (HND _ _ _ _ HHq) as ND.
    destruct (hm_apart asegs R HIA hq LBq LF mq HHq) as [HF BA]. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact XIN)) as (B0 & _ & BC & BI). cbn [fst snd] in B0, BC, BI.
    split; [exact B0|]. split; [exact BC|]. split; [destruct DIMG as [D1 D2]; clear - BI D1 D2; lia|].
    intros B j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
    - unfold mpd_keep in Hb. rewrite EO in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
      assert (NE : md_p dq <> B).
      { intros E. symmetry in E. revert E. apply (nodup_fst_neq LBq (md_p dq) (4 * md_n dq) B j ND XIN Hb).
        intros E. rewrite E in Hne. unfold blk_eqb in Hne. cbn [fst snd] in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne. }
      pose proof (blocks_apart_in2 (LBq ++ LF) _ _ _ _ BA ltac:(apply in_app_iff; left; exact XIN) ltac:(apply in_app_iff; left; exact Hb) NE) as K. clear - K. lia.
    - ddestruct (ep_fdata_sub2 LF (B, j) Hb) as ([FBq nq] & Hfb & H1 & H2). cbn [fst snd] in H1, H2.
      pose proof (ep_blocks_apart_app2 LBq LF (md_p dq, 4 * md_n dq) (FBq, nq) BA XIN Hfb) as K. cbn [fst snd] in K. clear - K H1 H2. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0>L10678603361.3L12760872139.7L18142789841.7L24842524269.2L30741553502.0L33306266156.8L39280637297.0L56329741247.6L57876306551.8L6445632415.8 00000;00R00g00n00o01P01Q01l02M02fS2SP2FR3FR0S1R3HIA1h2SP2FR3FR03TOPS1R3HIA1h1v2hk2HV3HVkS2dd2D0SS1R2SP2lo2FR6STKMAX4SLOK3NER4HSTKSS2SP2lo2FR6STKMAX4STK04LOSPS1R2SP2lo2FR6STKMAX4STK03LOS4LOSPS1R3HIA1h2dd1f2hk2HF4HFRk". (* [comment removed for export] *)
  #[using="EC TPV D0 SP64 SPA SLOK STK0 XOUW"] Lemma ep_free : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PENTRY,$9.P,(7=.$12.VR,VHIA,R1.)Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.PRET,$9.Pxt0,(13.&40.)Pxt1,(13.&40.)Pxt2,(13.&40.)Pc1,(13.&40.)Pxa0,(13.&40.)Pxa1,(13.&40.)Pxa2,(13.&40.)Pxa3,(13.&40.)Pxa4,(13.&40.)Pxa5,(13.&40.)Pxa6,(13.&40.)Pxa7,(13.&40.)Pc2,(13.&40.)Pc3,(13.&40.)Pc4,(13.&40.)Pc5,(13.&40.)Pc6,(13.&40.)Pc7,(13.&40.)Pc8,(13.&40.)Pc9,(13.&40.)Pc10,(13.&40.)Pc11,(13.&40.)Pxt3,(13.&40.)Pxt4,(13.&40.)Pxt5,(13.&40.)Pxt6,(13.&40.)PQ,P,$4?.SpP,(4:.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)P,(6.+40.VSTKMAX,)P,(6.(7.(28.$12.VR,VHIA,Vh,)(7.R27.$7>.))$62.)P,(6.(7.(29.$12.VR,VHIA,Vh,)(7.R27.(7?.Vdd,)))$63.)P,(=.(6.=R20.)(44.R20.(45.+2.+40.)))P,(24.$9.(47.R21.+2.)=)P,Ph',(11.$12.VR,VHIA,)PLB',(0.$1.)Pm',P,(13.&40.)(14.(13.&8.))Pt0',(13.&40.)Pt1',(13.&40.)Pt2',(13.&40.)Pa0',(13.&40.)Pa1',(13.&40.)Pa2',(13.&40.)Pa3',(13.&40.)Pa4',(13.&40.)Pa5',(13.&40.)Pa6',(13.&40.)Pa7',(13.&40.)Pt3',(13.&40.)Pt4',(13.&40.)Pt5',(13.&40.)Pt6',(13.&40.)P,(4:.(7.R3=.$7>.)(7.R3<.(7?.Vdd,))R12.R11.R10.R38.(36.R38.+1.==(23.(13.&40.))(39.R37.)$4=.)R36.R35.)(50.$12.(51.$12.VR,VHIA,R13.Vmo,)R1:.(52.(53.(54.&40.R35.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R31.R=.R<.R;.R:.R9.R8.R7.R6.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R5.R4.R3.R2.)VF,(54.&40.R35.)Vfc,(55.(13.&40.))R11.(56.$12.)))P,(24.(13.&40.)R1>.(54.&40.R27.))(50.$12.(51.$12.VR,VHIA,R2;.Vmo,)R9.(52.(53.(54.&40.R24.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R23.R22.R21.Vfpw,R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)VF,(54.&40.R2?.)Vfc,(55.(13.&40.))R29.(56.$12.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8). pose proof (arl_need_ecp_rt R) as NER.
    intros ENTRY HC. intros until Q. intros S HSTK HV HF HRET HRE K E0. subst xa0.
    ddestruct (ep_out v f hk LBk mk A1 d1 A2 d2 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    dpose S as (J & P & S1 & S2 & S12 & U1 & U2). pose proof P as (T1 & _). dpose S1 as (CW1 & SL1 & _).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    pose proof (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 J T1) as BLK.
    pose proof (HND _ _ _ _ HHk) as NDk.
    pose proof XM as [MAT SG1]. dpose MAT as (CX1 & AL1 & X01 & LL1 & NR1 & OW1).
    (* [comment removed for export] *)
    assert (SUBF : forall b, In b LB -> In b (mpi_free_LB (md_own d1) (md_p d1) (md_n d1) LBk)).
    { intros b Hb. unfold mpi_free_LB. destruct (md_own d1) eqn:EO; try exact (SUBk b Hb).
      ddestruct (BLK eq_refl) as (IN & _ & _ & _ & _ & NIN & _). destruct b as [B j]. apply In_lb_remove_keep; [exact (SUBk _ Hb)|].
      apply (nodup_fst_neq LBk (md_p d1) (4 * md_n d1) B j NDk IN (SUBk _ Hb)). intros E. apply NIN. rewrite <- E. exact Hb. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_free_stmtA in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (X := md_addr d1) (sw := Z_to_bv 64 (md_sg d1)) (n := md_n d1) (P := md_p d1) (limbs := md_limbs d1)
                     (pad := md_pad d1) (own := md_own d1) (lo := lo) (d := dd);
        rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      - exact HHk.
      - exact HK1.
      - exact MAT.
      - exact XNS.
      - rewrite XAD, HTk. eapply client_wrange_sp_mono; [| eapply client_wrange_mono; [exact CW1|]].
        + clear - FR0. lia.
        + intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBF b Hb)| right; exact Hb].
      - intros EO. rewrite XAD. pose proof (proj1 (proj2 XOS) EO) as K1. rewrite XAD in K1. exact K1.
      - exact STk.
      - exact LOS.
      - clear - SLOK HSTK NER. lia.
      - rewrite HTk. clear - TOP FR0. lia.
      - exact SPA.
      - exact TPV.
      - exact MIk.
      - exact (proj1 XAO).
      - clear - HV HVk. lia.
      - rewrite XAD. exact U1.
      - clear - HF HFRk. lia.
      - rewrite XAD. reflexivity. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_free_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & CX2).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (SP - FR)) in ST2, HP2 by exact SPR. rewrite XAD in HP2, CX2.
    rewrite (ret_pc_even RET HRET HRE).
    set (d1' := mkMPD A1 1 0 0 [] (md_pad d1) LNull).
    set (LB2 := mpi_free_LB (md_own d1) (md_p d1) (md_n d1) LBk) in *.
    assert (MX2 : mpd_at asegs m2 LB2 d1').
    { unfold d1', mpd_at, mpi_at. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. rewrite XAD in AL1, X01.
      split; [| left; reflexivity]. split; [exact CX2|]. split; [exact AL1|]. split; [exact X01|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; clear; lia| split; reflexivity]. }
    assert (OUT2 : mpd_out LBk d1 LB2 d1').
    { unfold mpd_out, d1', LB2, mpi_free_LB. cbn [md_addr md_own]. split; [symmetry; exact XAD|]. split; [discriminate|].
      destruct (md_own d1) eqn:EO.
      - split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|]. intros b Hb. unfold mpd_blk in Hb. rewrite EO in Hb. destruct Hb.
      - destruct (BLK eq_refl) as (IN & _).
        split; [intros b Hb; left; exact (In_lb_remove _ _ _ Hb)|].
        split.
        + intros [B j] Hb NB. apply In_lb_remove_keep; [exact Hb|].
          apply (nodup_fst_neq LBk (md_p d1) (4 * md_n d1) B j NDk IN Hb). intros E. apply NB. unfold mpd_blk. rewrite EO. left. symmetry. exact E.
        + intros b Hb Hb2. exfalso. unfold mpd_blk in Hb. rewrite EO in Hb. destruct Hb as [<-|[]]. exact (lb_remove_notin LBk (md_p d1) (4 * md_n d1) NDk Hb2).
      - exfalso. exact (XNS eq_refl). }
    assert (HP2' : presA asegs R (mpd_keep LBk d1) LF (SP - FR) (arl_stklo R) (hstkhi asegs R HIA hk) [(A1, A1 + 16)] mk m2).
    { unfold LB2, mpi_free_LB, mpi_free_X in HP2. destruct (md_own d1) eqn:EO.
      - unfold mpd_keep. rewrite EO. exact HP2.
      - destruct (BLK eq_refl) as (IN & _).
        eapply (presA_drop_fresh asegs R HIA hk (mpd_keep LBk d1) LF [(A1, A1 + 16)] (md_p d1) (4 * md_n d1) mk m2 (SP - FR)); [| exact (ep_keep_fresh hk LBk mk d1 HHk EO IN)| clear - LOS LOSP STK0; lia].
        eapply presA_weaken; [exact HP2| | intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl|].
        + intros [B j] Hb. unfold mpd_keep in Hb. rewrite EO in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
          apply In_lb_remove_keep; [exact Hb|].
          apply (nodup_fst_neq LBk (md_p d1) (4 * md_n d1) B j NDk IN Hb).
          intros E. rewrite E in Hne. unfold blk_eqb in Hne. cbn [fst snd] in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
        + intros x Hx. cbn [outside fst snd] in *. tauto.
      - exfalso. exact (XNS eq_refl). }
    destruct (epair_call R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 A2 d2 m2 h2 LB2 d1' (SP - FR) AVOL_CALL (fr_charge dd)
                J P S1 S2 S12 ltac:(clear - LOSP STK0; lia) ltac:(unfold AVOL_CALL; clear; lia) ltac:(unfold fr_charge; clear - D0; lia)
                MI2 ST2 HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 ltac:(intros b Hb; destruct Hb)) as [J2 P2].
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K. exact (conj J2 (conj P2 (conj S1 (conj S2 (conj S12 (conj U1 U2)))))).
    all: match goal with |- ?g => idtac "FREE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L10678603361.3 L12760872139.7 L14758432044.7 L15756354262.4 L19715409235.12L19725894707.8 L19725895507.13L19726054483.4 L33119465378.11L33134145218.13L38180633941.0 L46653260805.3 L5246360089.2  L57663894647.12L57663895319.14L57678575223.12L6463239664.9  L6463239824.13 L6463407504.6  L6473725072.12 L67020437154.3 00000;00R00o01=01>01?01@01R02202302402=02D02h02i02j02k02l02m02n037S2SP2FR3FR0S1R3HIA1h2SP2FR3FR03TOPS1R2SP2lo2FR6STKMAX4SLOK4HSTKS1R2lo3LOS3ALOFFFS2LB3LBk4HC244C24kS1R3HIA1h1g1v2hk2d12eA2eB2HV3HVkFSS1G2d12K1S2d12N1S1R3HIA1h2dd1g1f2hk2d12eA2eB2HF4HFRkFFFFFFS1G2d12K1". (* [comment removed for export] *)
  #[using="IMG EC slo TPV SP64 SPA SLOK STK0 UW0 XOUW SSH SLO1 SLO3 GRP DXG"] Lemma ep_mulmod : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PENTRY,$9.P,(80.$12.VR,VHIA,VMT,R1.VMC,)Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.PeA,$15.PeB,$15.PRET,$9.Pxt0,(13.&40.)Pxt1,(13.&40.)Pxt2,(13.&40.)Pc1,(13.&40.)Pxa0,(13.&40.)Pxa1,(13.&40.)Pxa2,(13.&40.)Pxa3,(13.&40.)Pxa4,(13.&40.)Pxa5,(13.&40.)Pxa6,(13.&40.)Pxa7,(13.&40.)Pc2,(13.&40.)Pc3,(13.&40.)Pc4,(13.&40.)Pc5,(13.&40.)Pc6,(13.&40.)Pc7,(13.&40.)Pc8,(13.&40.)Pc9,(13.&40.)Pc10,(13.&40.)Pc11,(13.&40.)Pxt3,(13.&40.)Pxt4,(13.&40.)Pxt5,(13.&40.)Pxt6,(13.&40.)PQ,P,$4?.SpP,(4:.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)P,(4>.R23.R22.R20.R1?.)P,(4>.R24.R23.R21.R1?.)P,(3:.R21.R20.)P,(43.VR,(37.R22.)+10.Vdd,)P,(43.VR,(37.R22.)+10.Vdd,)P,(5.(6.(7.VMC,+8.)(37.R24.))(6.(7.(37.R24.)+10.)VMC,))P,(5.(6.(7.VMC,+8.)(37.R24.))(6.(7.(37.R24.)+10.)VMC,))P,(5.(6.(7.R2:.+10.)VG,)(6.(7.VG,+<0.)R2:.))P,(6.+410.VSTKMAX,)P,(5?.(60.(61.$1.VLF,)#2.)#200.)P,(6.=(81.(35.R2<.)(35.R29.)(35.R28.)(35.(74.Vg,))))P,(6.=(82.(35.R2=.)(35.R2:.)(35.R29.)(35.(74.Vg,))Vdd,))P,(6.(7.(28.$12.VR,VHIA,Vh,)(7.R34.(81.(35.R2>.)(35.R2;.)(35.R2:.)(35.(74.Vg,)))))$62.)P,(6.(7.(29.$12.VR,VHIA,Vh,)(7.R34.(82.(35.R2?.)(35.R2<.)(35.R2;.)(35.(74.Vg,))Vdd,)))$63.)P,(6.(7.(7.(64.VLB,)+2.)$83.)$65.)P,(=.(6.=R2<.)(44.R2<.(45.+2.+40.)))P,(24.$9.(47.R2=.+2.)=)P,Ph',(11.$12.VR,VHIA,)PLB',(0.$1.)Pm',P,(13.&40.)(14.(13.&8.))Pd1',$15.Pr,$9.Pt0',(13.&40.)Pt1',(13.&40.)Pt2',(13.&40.)Pa1',(13.&40.)Pa2',(13.&40.)Pa3',(13.&40.)Pa4',(13.&40.)Pa5',(13.&40.)Pa6',(13.&40.)Pa7',(13.&40.)Pt3',(13.&40.)Pt4',(13.&40.)Pt5',(13.&40.)Pt6',(13.&40.)P,(4:.(7.R4<.(81.(35.R46.)(35.R43.)(35.R42.)(35.(74.Vg,))))(7.R4;.(82.(35.R46.)(35.R43.)(35.R42.)(35.(74.Vg,))Vdd,))R13.R12.R11.R47.R10.R45.R44.)P,(79.R4:.R47.R10.R11.)P,(6.(35.R12.)(84.(35.R48.)(35.R45.)(35.R44.)(35.(74.Vg,))))(50.$12.(51.$12.VR,VHIA,R16.Vmo,)R29.(52.(53.(54.&40.R44.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R11.R10.R?.Vfpw,R40.(54.&40.R12.)R>.R=.R<.R;.R:.R9.R8.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R7.R6.R5.R4.)VF,(54.&40.R44.)Vfc,(55.(13.&40.))R14.(56.$12.)))P,(24.(13.&40.)R2:.(54.&40.VG,))P,(24.(13.&40.)R2:.(54.&40.R36.))P,(24.(13.&40.)R2:.(54.&40.(37.R33.)))P,(24.(13.&40.)R2:.(54.&40.(37.R33.)))(50.$12.(51.$12.VR,VHIA,R3<.Vmo,)R18.(52.(53.(54.&40.R33.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R32.R31.R30.Vfpw,R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)VF,(54.&40.R40.)Vfc,(55.(13.&40.))R3:.(56.$12.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    intros ENTRY HC. intros until Q. intros S SA SB SAB UWA UWB AMC BMC AG HSTK HNF HPHI HFRC HV HF HC24 HRET HRE K E0 E1 E2 E3. subst xa0 xa1 xa2 xa3.
    ddestruct (ep_out v f hk LBk mk A1 d1 A2 d2 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (ep_opnd v f hk LBk mk A1 d1 A2 d2 eA S SA) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM & ANE).
    ddestruct (ep_opnd v f hk LBk mk A1 d1 A2 d2 eB S SB) as (BM & BSEP & BOS & BCR & BCRL & BAO & BIM & BNE).
    pose proof (ep_cnt24 v f hk LBk mk A1 d1 A2 d2 S) as C24k. dpose S as (J & P & S1 & S2 & S12 & U1 & U2). pose proof P as (T1 & _).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk [ck MCk] STk FRk].
    dpose GRP as (_ & _ & _ & _ & GCR & _).
    pose proof (ej_grp_pre R HIA h LB LF m SP lo FR FRAME XO MC EC MT v f hk LBk mk G g (SP - FR) dd J GRP DXG ltac:(clear - FR0; lia)) as GRPk.
    assert (OSk : ecp_out_sepA d1 G MC).
    { unfold ecp_out_sepA. rewrite XAD. split; [exact AG|]. split; [| ddestruct S1 as (_ & _ & _ & MS1); exact MS1].
      intros EO. ddestruct (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 J T1 EO) as (_ & N1 & _ & _ & _ & _ & FRA).
      destruct (fresh_apart_client R LB LF lo G 192 _ _ FRA GCR ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K1|K1]; [right| left]; clear - K1; lia. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold ecp_mul_mod_stmtA in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (dA := eA) (dB := eB) (G := G) (g := g) (cnt := ck) (lo := lo) (d := dd) (slo := slo);
        rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      all: first [ exact HHk | exact HK1 | exact HNF | exact GRPk | exact OSk | exact XM | exact AM | exact BM | exact ASEP | exact BSEP | exact SAB | exact XNS
                 | exact AOS | exact BOS | exact ACR | exact ACRL | exact BCR | exact BCRL | exact AMC | exact BMC | exact XWR | exact XLSq
                 | exact MCk | exact MCOK | exact STk | exact LOS | exact (ep_sshad v f hk LBk mk J) | exact SLO1 | exact SLO3 | exact SPA | exact TPV | exact MIk
                 | exact XAO | exact AAO | exact BAO | exact AIM | exact BIM | exact (ep_uwc v f hk LBk mk J) | (rewrite XAD; exact U1) | exact UWA | exact UWB | reflexivity
                 | (rewrite unsigned_lit by exact HRET; exact HRE)
                 | (rewrite HTk; clear - TOP FR0; lia) | (clear - SLOK HSTK; lia) | (clear - HV HVk; lia) | (clear - HF HFRk; lia) | (clear - HC24 C24k; lia)
                 | (rewrite XAD; reflexivity) | idtac ].
      all: match goal with |- ?g => idtac "MULMOD-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold ecp_mul_mod_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dY2 & r & cnt2 & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MY2 & OUT2 & FRA2 & GR2 & MCC2 & MR2 & SZ2).
    injection E as E1 E2. subst ms' mo'. rewrite XAD in HP2.
    rewrite ?(unsigned_lit (SP - FR)) in ST2, HP2 by exact SPR.
    rewrite (ret_pc_even RET HRET HRE).
    destruct (epair_call_mc v f hk LBk mk A1 d1 A2 d2 m2 h2 LB2 dY2 _ _
                J P S1 S2 S12 HPHI HFRC MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MY2 OUT2 FRA2 ltac:(exists cnt2; exact MCC2)) as [J2 P2].
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [| exact MR2| exact SZ2].
    exact (conj J2 (conj P2 (conj S1 (conj S2 (conj S12 (conj U1 U2)))))).
    all: match goal with |- ?g => idtac "MULMOD-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308546384.3000008S1e1K2N1". (* [comment removed for export] *)
  #[using="IMG EC STKMAX SP64 SPA SLOK STK0"] Lemma ep_rd : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.Pe,$15.P,(4:.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(4>.R6.R5.R3.R2.)(=.(2;.$12.R8.R9.R3.)(=.P,(24.$30.(31.R3.)$32.)(44.=(33.R4.))(=.(85.$12.(40.VR,)(27.$12.VR,VHIA,R:.)R8.(37.R3.)+10.)(=.P,(6.+1.(35.R3.))(85.$12.(40.VR,)(27.$12.VR,VHIA,R;.)R9.(33.R4.)(34.+4.(35.R4.)))(=.(5.(6.(7.(37.R3.)+10.)Vlo,)(6.(19.VSP,VFR,)(37.R3.)))P,(6.+1.(35.R3.))(5.(6.(7.(33.R4.)(34.+4.(35.R4.)))Vlo,)(6.(19.VSP,VFR,)(33.R4.))))))))")
(* [comment removed for export] *).
  Proof.
    intros v f hk LBk mk A1 d1 A2 d2 e S SE.
    ddestruct (ep_opnd v f hk LBk mk A1 d1 A2 d2 e S SE) as (EM & _ & (_ & _ & _ & OS4 & OS5) & _ & _ & [AOs AOl] & _ & _).
    destruct S as (J & _). pose proof (ej_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HHk.
    pose proof EM as [(_ & _ & _ & _ & _ & OW) _].
    assert (NN : 1 <= md_n e -> md_own e <> LNull) by (intros N1 C; rewrite C in OW; destruct OW as [_ K]; clear - K N1; lia).
    split; [exact EM|].
    split.
    { intros EO. rewrite EO in OW. ddestruct OW as (_ & IN & _).
      destruct (hm_apart asegs R HIA hk LBk LF mk HHk) as [HF _]. rewrite Forall_forall in HF.
      destruct (HF _ ltac:(apply in_app_iff; left; exact IN)) as (B0 & _). exact B0. }
    split; [exact AOs|].
    split.
    { intros N1. destruct (md_own e) eqn:EO; [exfalso; exact (NN N1 eq_refl)| | exact (AOl eq_refl)].
      ddestruct OW as (_ & IN & _). eapply hm_aobj_block; [exact HHk| exact IN]. }
    split; [exact OS4|]. intros N1. exact (OS5 (NN N1)).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L35653327737.8L43638642170.6L60098763854.300000K00f010S1R3HIA1h2SP2lo2FR3FR04SPHIS2SP2lo2FR6STKMAX4LOSP4HSTKS1R2lo3LOS". (* [comment removed for export] *)
  #[using="IMG EC SP64 SPA SLOK STK0"] Lemma ep_cmp : ltac2:(CDefT.buildp (gd_tbl_A_ecp_pair ()) "PENTRY,$9.P,(86.$12.(40.VR,)R1.)Pv,$9.Pf,$9.Phk,(11.$12.VR,VHIA,)PLBk,(0.$1.)Pmk,P,(13.&40.)(14.(13.&8.))PA1,$9.Pd1,$15.PA2,$9.Pd2,$15.PeX,$15.PeY,$15.PRET,$9.Pxt0,(13.&40.)Pxt1,(13.&40.)Pxt2,(13.&40.)Pc1,(13.&40.)Pxa0,(13.&40.)Pxa1,(13.&40.)Pxa2,(13.&40.)Pxa3,(13.&40.)Pxa4,(13.&40.)Pxa5,(13.&40.)Pxa6,(13.&40.)Pxa7,(13.&40.)Pc2,(13.&40.)Pc3,(13.&40.)Pc4,(13.&40.)Pc5,(13.&40.)Pc6,(13.&40.)Pc7,(13.&40.)Pc8,(13.&40.)Pc9,(13.&40.)Pc10,(13.&40.)Pc11,(13.&40.)Pxt3,(13.&40.)Pxt4,(13.&40.)Pxt5,(13.&40.)Pxt6,(13.&40.)PQ,P,$4?.SpP,(4:.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)P,(4>.R23.R22.R20.R1?.)P,(4>.R24.R23.R21.R1?.)P,(6.+10.VSTKMAX,)P,(=.(6.=R20.)(44.R20.(45.+2.+40.)))P,(24.$9.(47.R21.+2.)=)P,Pm',P,(13.&40.)(14.(13.&8.))Pt0',(13.&40.)Pt1',(13.&40.)Pt2',(13.&40.)Pa1',(13.&40.)Pa2',(13.&40.)Pa3',(13.&40.)Pa4',(13.&40.)Pa5',(13.&40.)Pa6',(13.&40.)Pa7',(13.&40.)Pt3',(13.&40.)Pt4',(13.&40.)Pt5',(13.&40.)Pt6',(13.&40.)P,(4:.R3<.R3;.R3:.R39.R?.R37.R36.R35.R34.)(50.$12.(51.$12.VR,VHIA,R3;.Vmo,)R17.(52.(53.(54.&40.R32.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R?.R>.R=.Vfpw,R2>.(54.&40.(87.(19.(73.R34.)(73.R33.))))R<.R;.R:.R9.R8.R7.R6.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R5.R4.R3.R2.)VF,(54.&40.R32.)Vfc,(55.(13.&40.))R10.(56.$12.)))P,(24.(13.&40.)R1>.(54.&40.(37.R25.)))P,(24.(13.&40.)R1>.(54.&40.(37.R25.)))(50.$12.(51.$12.VR,VHIA,R2>.Vmo,)R:.(52.(53.(54.&40.R25.)(54.&40.(19.VSP,VFR,))Vgp,Vtp,R24.R23.R22.Vfpw,R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)VF,(54.&40.R32.)Vfc,(55.(13.&40.))R2<.(56.$12.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ep_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    intros ENTRY HQ. intros until Q. intros S SX SY HSTK HRET HRE K E0 E1. subst xa0 xa1.
    ddestruct (ep_rd v f hk LBk mk A1 d1 A2 d2 eX S SX) as (XM & XP0 & XOs & XOl & XSs & XSl).
    ddestruct (ep_rd v f hk LBk mk A1 d1 A2 d2 eY S SY) as (YM & YP0 & YOs & YOl & YSs & YSl).
    pose proof S as (J & _). pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (SCS : crange (hcs asegs R HIA hk) lo (SP - FR - lo)).
    { eapply crange_sub; [exact (hcs_stack asegs R HIA hk)| clear - LOS; lia| rewrite HSk; clear - SPHI FR0; lia]. }
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo).
    { unfold mpi_cmp_mpi_stmtA in HQ.
      eapply HQ with (CS := hcs asegs R HIA hk) (LB := LBk) (dX := eX) (dY := eY) (lo := lo); rewrite ?(unsigned_lit (SP - FR)) by exact SPR;
        first [ exact XM | exact YM | exact XP0 | exact YP0 | exact MIk | exact (art_alwf asegs R HIA) | exact (hcs_ok asegs R HIA hk) | exact (hm_abase asegs R HIA hk LBk LF mk HHk)
              | exact XOs | exact YOs | exact XOl | exact YOl | exact STk | exact LO0 | exact SPA | exact SCS | exact XSs | exact YSs | exact XSl | exact YSl | reflexivity
              | (clear - LOSP HSTK; lia) | idtac ].
      all: match goal with |- ?g => idtac "CMP-PRE-LEFT:" g end. }
    intros ms' PO. unfold mpi_cmp_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'.
    rewrite ?(unsigned_lit (SP - FR)) in MU2, ST2 by exact SPR.
    rewrite (ret_pc_even RET HRET HRE).
    eapply K. exact (ep_scratch v f hk LBk mk A1 d1 A2 d2 m2 S MU2 WM2 MI2 ST2).
    all: match goal with |- ?g => idtac "CMP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End EP.
