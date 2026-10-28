(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Export MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_rt_facts A_alloc_lib A_mpi_stmtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Export A_mpi_opnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_journey () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "JA.XJA"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "JA.FBA"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Nat.mul"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "JA.XDA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.binop_keep"; "Corelib.Init.Datatypes.snd"; "JA.BJA"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.w_client"].


Definition blk_eq_dec (x y : blk) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition limb_own_eq_dec (a b : limb_own) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* [comment removed for export] *)
Section JA.
  Variable segs : list Segment.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA segs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  (* [comment removed for export] *)
  Variables (h : HST segs R HIA) (LB LF : list blk) (m : mem) (dX : mpd) (sp : word) (lo FS : Z) (FRAME : list cell).
  Local Notation SP := (bv_unsigned sp).
  Local Notation X := (md_addr dX).

  (* [comment removed for export] *)
  Record JCA : Prop := {
    jca_NEEDR : 0 <= arl_need_rt R;
    jca_HND : forall h LB LF m, HM segs R HIA h LB LF m -> List.NoDup (map fst LB);
    jca_DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L;
    jca_ROIMG : forall a, ro_addr segs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L;
    jca_HH : HM segs R HIA h LB LF m;
    jca_MX : mpd_at segs m LB dX;
    jca_NST : md_own dX <> LStatic;
    jca_XW : mpd_writableA R LB LF SP (htop segs R HIA h) dX;
    jca_XLS : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ SP <= md_p dX;
    jca_LOS : arl_stklo R <= lo;
    jca_FS16 : 16 <= FS;
    jca_SLO : lo <= SP - FS - arl_need_rt R;
    jca_TOP : SP <= htop segs R HIA h;
    jca_SPA : SP mod 16 = 0;
    jca_FSZ : Z.of_nat (cells_size FRAME) = FS }.
  Hypothesis JC : JCA.
  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].

  (* [comment removed for export] *)
  Record XJA (EX : list blk) (v f : Z) (hc : HST segs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) : Prop := {
    xa_mi : mem_inv segs mc;
    xa_stk : stk segs mc lo (SP - FS);
    xa_fr : rw_cells segs mc (SP - FS) FRAME;
    xa_hm : HM segs R HIA hc (EX ++ LBc) LF mc;
    xa_top : htop segs R HIA hc = htop segs R HIA h;
    xa_stkhi : hstkhi segs R HIA hc = hstkhi segs R HIA h;
    xa_flag : hflag segs R HIA hc = hflag segs R HIA h;
    xa_hcs : forall x, hcs segs R HIA h x -> hcs segs R HIA hc x;
    xa_vol : havol segs R HIA hc <= havol segs R HIA h + v;
    xa_frs : hfr segs R HIA hc <= hfr segs R HIA h + f;
    xa_X : mpd_at segs mc LBc dXc;
    xa_addr : md_addr dXc = md_addr dX;
    xa_pad : md_pad dXc = md_pad dX;
    xa_nst : md_own dXc <> LStatic;
    xa_out : mpd_out LB dX LBc dXc;
    xa_fresh : forall b, In b (mpd_blk dXc) -> In b (mpd_blk dX) \/ ~ In b LB;
    xa_freshA : forall b, In b (mpd_blk dXc) -> In b (mpd_blk dX) \/ fresh_apart R (mpd_keep LB dX) LF (fst b) (snd b);
    xa_pres : presA segs R (mpd_keep LB dX) LF SP (arl_stklo R) (hstkhi segs R HIA h) [(X, X + 16)] m mc;
    xa_aobjX : aobj segs AL (hcs segs R HIA hc) mc X 16;
    (* [comment removed for export] *)
    xa_XP : md_own dXc = LHeap -> X + 16 <= md_p dXc \/ md_p dXc + 4 * md_n dXc <= X;
    (* [comment removed for export] *)
    xa_XLS : md_own dXc <> LNull -> md_p dXc + 4 * md_n dXc <= lo \/ SP <= md_p dXc;
    (* [comment removed for export] *)
    xa_nmono : md_n dX <= md_n dXc
  }.

  (* [comment removed for export] *)
  #[using="segs HIA h LB LF m FRAME JC"] Lemma jca_facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "(0.(1.=Vlo,)(0.(1.Vlo,(2.(3.&40.Vsp,)VFS,))(0.(4.(3.&40.Vsp,)(5.+2.+40.))(0.(1.(6.(7.VR,))(8.VR,))(0.(4.+1000.(6.(7.VR,)))(0.(4.=(9.VdX,))(0.(1.(:.(9.VdX,)+10.)(5.+2.+40.))(0.(;.$<.(=.(9.VdX,)+8.)=)(0.(>.(1.(:.(9.VdX,)+10.)Vlo,)(1.(3.&40.Vsp,)(9.VdX,)))(0.(;.$<.(?.(10.(11.&40.)(12.VdX,)))(13.VdX,))(0.(1.=(13.VdX,))(1.(13.VdX,)+2710.))))))))))))")
(* [comment removed for export] *).
  Proof.
    jc_open. pose proof (art_lo segs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof MX as [(CX & XAL & X0 & LEN & NR & _) _]. pose proof (rw_cells_bound _ _ _ _ CX) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add] in XB.
    destruct XW as [CW DXP].
    assert (DSX : X + 16 <= lo \/ SP <= X).
    { eapply (client_wrange_where_A segs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO NEEDR FS16; lia]. }
    unfold MPI_MAX_LIMBS in NR. repeat split; try assumption; first [clear - NR; lia | clear - XB; lia | clear - ALO ACP SPR LOS SLO NEEDR FS16; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.P,(19.R7.R6.R5.R4.R3.R2.R1.)(0.(1:.$<.(1;.(1<.$<.$<.)$<.(1=.$<.$<.)(1>.$15.R8.R4.)))(0.(;.$<.(?.(10.(11.&40.)(12.R2.)))(13.R2.))(0.(0.(1.=(13.R2.))(1.(13.R2.)+2710.))(0.(>.(;.$<.(1?.R2.)+1.)(;.$<.(1?.R2.)-1.))(0.(20.Vsegs,R3.(9.VdX,)(21.(22.R2.)(23.&40.(1?.R2.))(13.R2.)(24.VdX,)))(0.P,(;.$25.(26.R2.)$27.)(0.(;.$<.(22.R3.)=)(0.(;.$<.(13.R3.)=)(;.(14.(11.&40.))(12.R3.)(28.(11.&40.)))))P,(29.(;.$25.(26.R2.)$27.))(0.(;.$25.(26.R3.)$2:.)(0.(1.+1.(13.R3.))(0.(2;.(1<.$<.$<.)(2<.$<.$<.(22.R3.)(2=.+4.(13.R3.)))R5.)(0.(;.$<.(=.(22.R3.)+10.)=)(0.(2>.Vsegs,R4.(22.R3.)(12.R3.))(0.(4.=(22.R3.))(0.(1.(:.(22.R3.)(2=.+4.(13.R3.)))(6.(7.VR,)))(0.(>.(1.(:.(22.R3.)(2=.+4.(13.R3.)))(2?.(7.VR,)))(1.(30.(7.VR,))(22.R3.)))(0.(31.Vsegs,(32.VR,)(33.Vsegs,VR,VHIA,R6.)R4.(22.R3.)(2=.+4.(13.R3.)))(1.(:.(:.(22.R3.)(2=.+4.(13.R3.)))+8.)(5.+2.+2?.)))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros EX v f hc LBc mc dXc J. pose proof (xa_hm _ _ _ _ _ _ _ J) as HHc.
    destruct (hm_apart segs R HIA hc (EX ++ LBc) LF mc HHc) as [HF BA]. rewrite Forall_forall in HF.
    split; [exact (HND _ _ _ _ HHc)|].
    pose proof (xa_X _ _ _ _ _ _ _ J) as [(CX & XAL & X0 & LEN & NR & OWN) SG]. rewrite (xa_addr _ _ _ _ _ _ _ J), (xa_pad _ _ _ _ _ _ _ J) in CX.
    unfold MPI_MAX_LIMBS in NR.
    split; [exact LEN|]. split; [exact NR|]. split; [exact SG|]. split; [exact CX|].
    split.
    { intros EO. rewrite EO in OWN. destruct OWN as [EP EN]. split; [exact EP|]. split; [exact EN|].
      destruct (md_limbs dXc); [reflexivity| exfalso; cbn in LEN; clear - LEN EN; lia]. }
    intros NN. pose proof (xa_nst _ _ _ _ _ _ _ J) as NS. destruct (md_own dXc); [exfalso; exact (NN eq_refl)| | exfalso; exact (NS eq_refl)].
    ddestruct OWN as (O1 & O2 & O3 & O4). assert (O2' : In (md_p dXc, 4 * md_n dXc) ((EX ++ LBc) ++ LF)) by (apply in_or_app; left; apply in_or_app; right; exact O2).
    destruct (HF _ O2') as (R0 & R1 & R2 & R3). cbn in R0, R1, R2, R3.
    split; [reflexivity|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. split; [exact R0|]. split; [exact R2|]. split; [exact R3|].
    split; [eapply hm_aobj_block; [exact HHc| apply in_or_app; right; exact O2]|].
    eapply blk_top47; [exact HHc| apply in_or_app; right; exact O2].
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_cwX : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.P,(19.R7.R6.R5.R4.R3.R2.R1.)(34.(7.VR,)(1>.$15.R4.(35.VLF,))(3.&40.Vsp,)(36.Vsegs,VR,VHIA,Vh,)(9.VdX,)+10.)")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros EX v f hc LBc mc dXc J. destruct XW as [XCW XP].
    eapply client_wrange_mono; [exact (client_wrange_keep L LB LF _ _ dX X 16 XCW XP)|].
    intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
    pose proof (xa_out _ _ _ _ _ _ _ J) as (_ & _ & _ & O4 & _). apply O4; [eapply In_mpd_keep; exact Hb|].
    unfold mpd_keep in Hb. unfold mpd_blk. destruct (md_own dX); try (intros []; fail).
    apply filter_In in Hb. destruct Hb as [_ Hne]. intros [E|[]]. rewrite <- E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
  Qed.

  #[using="JC"] Lemma xa_crX : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PSP',$<.P,(19.R8.R7.R6.R5.R4.R3.R2.)P,(1.R2.(3.&40.Vsp,))(37.(7.VR,)(1>.$15.(1>.$15.R:.R6.)(35.VLF,))R3.(9.VdX,)+10.)")
(* [comment removed for export] *).
  Proof.
    intros EX v f hc LBc mc dXc SP' J LE. eapply client_range_inside; [eapply client_wrange_sp_mono; [exact LE| exact (xa_cwX _ _ _ _ _ _ _ J)]| | clear; lia| clear; lia].
    intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; exact Hb].
  Qed.

  #[using="Type"] Lemma xa_blocks_orig : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.Pb,$15.P,(19.R8.R7.R6.R5.R4.R3.R2.)P,(2;.$15.R2.VLB,)(>.(2;.$15.R3.R6.)(2;.$15.R3.(38.VdX,)))")
(* [comment removed for export] *).
  Proof.
    intros EX v f hc LBc mc dXc b J Hb. pose proof (proj1 (proj2 (proj2 (proj2 (xa_out _ _ _ _ _ _ _ J))))) as O4.
    unfold mpd_blk in *. destruct (md_own dX); [left| | left].
    1,3: apply O4; [exact Hb| intros []].
    destruct b as [q k]. destruct (blk_eq_dec (q, k) (md_p dX, 4 * md_n dX)) as [->|NE]; [right; left; reflexivity|].
    left. apply O4; [exact Hb|]. intros [E|[]]. exact (NE (eq_sym E)).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma xa_keep_sub : forall EX v f hc LBc mc dXc b, XJA EX v f hc LBc mc dXc -> In b (mpd_keep LB dX) -> In b LBc.
  Proof.
    intros EX v f hc LBc mc dXc b J Hb. pose proof (proj1 (proj2 (proj2 (proj2 (xa_out _ _ _ _ _ _ _ J))))) as O4.
    apply O4; [eapply In_mpd_keep; exact Hb|].
    unfold mpd_keep in Hb. unfold mpd_blk. destruct (md_own dX); try (intros []; fail).
    apply filter_In in Hb. destruct Hb as [_ Hne]. intros [E|[]]. rewrite <- E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_start : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pm1,P,(11.&40.)(17.(11.&8.))P,(39.Vsegs,VR,VHIA,Vh,VLB,VLF,R1.)P,(3:.Vsegs,R2.)P,(3;.Vsegs,R3.Vlo,(2.(3.&40.Vsp,)VFS,))P,(20.Vsegs,R4.(2.(3.&40.Vsp,)VFS,)VFRAME,)P,(31.Vsegs,(32.VR,)(33.Vsegs,VR,VHIA,Vh,)R5.(9.VdX,)+10.)P,(3<.(3=.(1<.$<.$<.)(2<.$<.$<.Vlo,(3.&40.Vsp,))(28.(1<.$<.$<.)))Vm,R6.)P,(3>.Vsegs,Vm,R7.)(19.(28.$15.)==Vh,VLB,R8.VdX,)")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros m1 HH1 MI1 ST1 FR1 OX1 MU WM. destruct XW as [CW DXP].
    constructor; cbn [app]; try assumption; try reflexivity.
    - intros x Hx; exact Hx.
    - clear; lia.
    - clear; lia.
    - eapply mpd_at_munch_any; [exact MX| exact MU| exact WM| cbn [disjoint_from fst snd]; clear - DSX; lia|].
      intros NN. cbn [disjoint_from fst snd]. pose proof (XLS NN). clear - H. lia.
    - apply mpd_out_refl. exact NST.
    - intros b Hb; left; exact Hb.
    - intros b Hb; left; exact Hb.
    - apply presA_nil_any. eapply (presA_tail0 segs R HIA h LB); [exact HH| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_limbs : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PW,(14.$3?.)Pm',P,(11.&40.)(17.(11.&8.))Pxs',(14.(11.&40.))P,(19.R:.R9.R8.R7.R6.R5.R4.)P,(3<.R4.R6.R3.)P,(3>.Vsegs,R7.R4.)P,(3:.Vsegs,R5.)P,(3;.Vsegs,R6.Vlo,(2.(3.&40.Vsp,)VFS,))P,(39.Vsegs,VR,VHIA,R<.(1>.$15.R?.R;.)VLF,R7.)P,Pa,$<.P,(29.(40.R:.R1.))(>.(0.(;.$25.(26.R<.)$2:.)(0.(1.(22.R<.)R2.)(4.R2.(:.(22.R<.)(2=.+4.(13.R<.))))))(0.(1.Vlo,R2.)(4.R2.(2.(3.&40.Vsp,)VFS,))))P,(41.R:.(2.(3.&40.Vsp,)VFS,)VFS,)P,(41.R;.(9.VdX,)+10.)P,(2>.Vsegs,R;.(22.R=.)R:.)P,(;.$42.(10.(11.&40.)R;.)(10.(11.&40.)(12.R>.)))(19.R15.R14.R13.R12.R11.R=.(43.(9.R?.)(1?.R?.)(13.R?.)(22.R?.)R<.(24.R?.)(26.R?.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros EX v f hc LBc mc dXc W m' xs' J MU WM MI' ST' HH' HW DF DS ARR' LEN'.
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    pose proof (hcs_ok segs R HIA hc) as CSOKc. pose proof (hm_top segs R HIA h LB LF m HH) as HTOP0.
    assert (SCSc : crange (hcs segs R HIA hc) lo (SP - lo)).
    { eapply crange_sub; [exact (hcs_stack segs R HIA hc)| exact LOS| rewrite HS1; clear - HTOP0 TOP; lia]. }
    assert (OUTW : forall a, (md_own dXc <> LHeap \/ md_p dXc + 4 * md_n dXc <= a \/ a < md_p dXc) -> (a < lo \/ SP - FS <= a) -> outside W a).
    { intros a H1 H2. destruct (outside_dec W a) as [O|NO]; [exact O|]. exfalso. destruct (HW a NO) as [[EO Rg]|Rg]; [| clear - Rg H2; lia].
      destruct H1 as [H1|H1]; [exact (H1 EO)| clear - Rg H1; lia]. }
    (* [comment removed for export] *)
    assert (HP' : presA segs R (mpd_keep LB dX) LF SP (arl_stklo R) (hstkhi segs R HIA h) [(X, X + 16)] mc m').
    { destruct (limb_own_eq_dec (md_own dXc) LHeap) as [EO|NEO].
      - ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
        (* [comment removed for export] *)
        assert (TAILP : presA segs R (mpd_keep LB dX) LF SP (arl_stklo R) (hstkhi segs R HIA h)
                          [(md_p dXc, md_p dXc + 4 * md_n dXc); (X, X + 16)] mc m').
        { rewrite <- HS1.
          eapply (presA_weaken segs R (EX ++ LBc) (mpd_keep LB dX) LF LF SP SP (arl_stklo R) (arl_stklo R) (hstkhi segs R HIA hc) (hstkhi segs R HIA hc)
                    [(md_p dXc, md_p dXc + 4 * md_n dXc); (X, X + 16)]);
            [| intros b Hb; apply in_or_app; right; exact (xa_keep_sub _ _ _ _ _ _ _ _ J Hb)| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia
             | intros y Hy; exact Hy].
          eapply (presA_drop_below segs R HIA hc (EX ++ LBc) LF _ lo SP _ mc m'); [exact HH1| | clear; lia| exact LOS].
          eapply (presA_of_munch segs R (EX ++ LBc) LF _ _ _ _ mc m' (hcs segs R HIA hc) CSOKc);
            [| intros c0 Hc; eapply cshd_hcs; [exact HH1| | exact Hc]; clear; lia| | exact WM].
          + unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (SP - lo)) with SP by (clear; lia); exact SCSc|].
            apply Forall_cons; [cbn [fst snd]; replace (md_p dXc + 4 * md_n dXc - md_p dXc) with (4 * md_n dXc) by (clear; lia); eapply aobj_crange; exact OP|].
            apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX1| apply Forall_nil].
          + eapply munch_weaken; [| exact MU]. intros a Ha. cbn [outside fst snd] in Ha. apply OUTW; clear - Ha LOSP FS16; lia. }
        destruct (FRA1 (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [HbX|HFR].
        + (* [comment removed for export] *)
          assert (EOX : md_own dX = LHeap /\ md_p dX = md_p dXc /\ md_n dX = md_n dXc).
          { unfold mpd_blk in HbX. destruct (md_own dX); try (destruct HbX; fail). destruct HbX as [E|[]]. injection E as E1 E2. split; [reflexivity| split; [exact E1| clear - E2 NR NR1; lia]]. }
          ddestruct EOX as (EOd & EP & EN).
          pose proof MX as [(_ & _ & _ & _ & _ & OWd) _]. rewrite EOd in OWd. ddestruct OWd as (_ & XINd & _).
          eapply (presA_drop_freed segs R HIA h LB LF (mpd_keep LB dX) [(X, X + 16)] (md_p dXc) (4 * md_n dXc) m mc m');
            [exact HH| rewrite <- EP, <- EN; exact XINd| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS LOSP FS16; lia| exact TAILP].
          intros b xb Hb Hr. unfold mpd_keep in Hb. rewrite EOd in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
          split; [exact Hb|]. intros E. rewrite E, <- EP, <- EN in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
        + (* [comment removed for export] *)
          eapply (presA_drop_fresh segs R HIA h (mpd_keep LB dX) LF [(X, X + 16)] (md_p dXc) (4 * md_n dXc) mc m' SP); [exact TAILP| exact HFR| clear - LOS LOSP FS16; lia].
      - (* [comment removed for export] *)
        apply presA_nil_any. rewrite <- HS1.
        eapply (presA_tail0 segs R HIA hc (EX ++ LBc)); [exact HH1| intros b Hb; apply in_or_app; right; exact (xa_keep_sub _ _ _ _ _ _ _ _ J Hb)| exact LOS| rewrite HT1; exact TOP| | exact WM].
        eapply munch_weaken; [| exact MU]. intros a Ha. cbn [outside fst snd] in Ha. apply OUTW; [left; exact NEO| clear - Ha LOSP FS16; lia]. }
    constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption.
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM| rewrite FSZ; exact DF].
    - pose proof MX1 as [(CX & XAL' & X0' & LEN0 & NR0 & OW) SG]. split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split.
      { eapply rw_cells_transport; [exact CX| exact MU| exact WM|]. unfold mpi_cells; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite AD1. exact DS. }
      split; [exact XAL'|]. split; [exact X0'|]. split; [rewrite <- LEN0, LEN'; reflexivity|]. split; [exact NR0|].
      destruct (md_own dXc) eqn:EO2; [exact OW| | exfalso; first [exact (NS1 eq_refl)| exact (NS1 EO2)]]. ddestruct OW as (O1 & O2 & O3 & O4). split; [exact O1|]. split; [exact O2|]. split; [exact O3| exact ARR'].
    - eapply presA_trans; [exact HPX1| exact HP'].
    - eapply (aobj_munch segs AL _ CSOKc W mc m'); [| exact MU| exact OX1].
      unfold w_client. rewrite Forall_forall. intros [a b] Hin x Hx. cbn [fst snd] in Hx.
      assert (NO : ~ outside W x).
      { clear - Hin Hx. induction W as [|[c d] W IH]; [destruct Hin|]. cbn. destruct Hin as [E|Hin]; [injection E as -> ->; lia| intros [_ O]; exact (IH Hin O)]. }
      destruct (HW x NO) as [[EO Rg]|Rg].
      + ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & _ & _ & _ & _ & _ & _ & _ & OP & _). eapply (aobj_crange segs AL); [exact OP| exact Rg].
      + apply SCSc. clear - Rg LOSP FS16. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_scratch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.Pwlo,$<.Pwhi,$<.Pm',P,(11.&40.)(17.(11.&8.))P,(19.R:.R9.R8.R7.R6.R5.R4.)P,(3<.(3=.(1<.$<.$<.)(2<.$<.$<.R4.R3.)(28.(1<.$<.$<.)))R6.R2.)P,(3>.Vsegs,R7.R3.)P,(3:.Vsegs,R4.)P,(3;.Vsegs,R5.Vlo,(2.(3.&40.Vsp,)VFS,))P,(39.Vsegs,VR,VHIA,R<.(1>.$15.R?.R;.)VLF,R6.)P,(1.Vlo,R9.)P,(1.R9.(2.(3.&40.Vsp,)VFS,))(19.R12.R11.R10.R?.R>.R9.(43.(9.R<.)(1?.R<.)(13.R<.)(22.R<.)(12.R<.)(24.R<.)(26.R<.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros EX v f hc LBc mc dXc wlo whi m' J MU WM MI' ST' HH' W1 W2.
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    eapply (xa_limbs EX v f hc LBc mc dXc [(wlo, whi)] m' (md_limbs dXc) J MU WM MI' ST' HH').
    - intros a NO. right. cbn [outside] in NO. clear - NO W1 W2. lia.
    - cbn [disjoint_from]. split; [clear - W2; lia| exact I].
    - cbn [disjoint_from]. split; [clear - W1 W2 DSX FS16 LOSP; lia| exact I].
    - destruct (limb_own_eq_dec (md_own dXc) LNull) as [EO|NEO].
      + ddestruct (OWN0 EO) as (EP & EN & EL). rewrite EP, EL. unfold u32arr, bytes_at, wr_at. cbn [u32s flat_map length Z.of_nat Z.mul].
        split; (split; [clear; lia| split; [clear; lia| intros i Hi; exfalso; clear - Hi; lia]]).
      + ddestruct (OWN1 NEO) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
        eapply (u32arr_transport segs [(wlo, whi)] mc m'); [exact XARR| exact MU| exact WM|].
        cbn [disjoint_from]. split; [| exact I]. pose proof (XLS1 NEO) as XL. clear - XL W1 W2 LEN1 LOSP FS16 N1. lia.
    - reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_transport : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)PEX2,(14.$15.)Pv,$<.Pf,$<.Pdv,$<.Pdf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.Pm2,P,(11.&40.)(17.(11.&8.))Ph2,(16.Vsegs,VR,VHIA,)P,(19.R<.R:.R9.R6.R5.R4.R3.)P,(3:.Vsegs,R3.)P,(3;.Vsegs,R4.Vlo,(2.(3.&40.Vsp,)VFS,))P,(44.Vsegs,VR,(1>.$15.R?.R8.)VLF,(2.(3.&40.Vsp,)VFS,)(8.VR,)(45.Vsegs,VR,VHIA,R9.)(28.$3?.)R7.R5.)P,(;.$<.(36.Vsegs,VR,VHIA,R5.)(36.Vsegs,VR,VHIA,R:.))P,(;.$<.(45.Vsegs,VR,VHIA,R6.)(45.Vsegs,VR,VHIA,R;.))P,(;.$<.(46.Vsegs,VR,VHIA,R7.)(46.Vsegs,VR,VHIA,R<.))P,Px,$<.P,(33.Vsegs,VR,VHIA,R>.R1.)(33.Vsegs,VR,VHIA,R:.R2.)P,(1.(47.Vsegs,VR,VHIA,R9.)(:.(47.Vsegs,VR,VHIA,R>.)R10.))P,(1.(48.Vsegs,VR,VHIA,R:.)(:.(48.Vsegs,VR,VHIA,R?.)R10.))P,(39.Vsegs,VR,VHIA,R;.(1>.$15.R15.R?.)VLF,R<.)(19.R16.(:.R15.R13.)(:.R14.R12.)R<.R10.R=.R>.)")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros EX EX2 v f dv df hc LBc mc dXc m2 h2 J MI2 ST2 HP HT2 HS2 HF2 HCS2 HV2 HFR2 HH2.
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    constructor; try assumption.
    - eapply (presA_rw_cells segs R); [exact HP| exact FR1| rewrite FSZ; apply client_range_stack; clear; lia| cbn; exact I].
    - rewrite HT2; exact HT1.
    - rewrite HS2; exact HS1.
    - rewrite HF2; exact HF1.
    - intros x Hx. apply HCS2, HCS1, Hx.
    - clear - HV1 HV2. lia.
    - clear - HFR1 HFR2. lia.
    - eapply (mpd_at_heap_presx segs L mc m2 LBc ((EX ++ LBc) ++ fdata LF) LBc (SP - FS) []);
        [exact MX1| exact (presA_presx segs R _ _ _ _ _ _ _ _ HP)| exact MI1| exact MI2| rewrite AD1; eapply xa_crX; [exact J| clear - FS16; lia]| | cbn; exact I| intros _; cbn; exact I|].
      + intros EO. ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & _). eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; exact XIN| clear; lia| clear; lia].
      + intros b Hb. pose proof MX1 as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hb. destruct (md_own dXc); try (destruct Hb; fail).
        destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)).
    - eapply presA_trans; [exact HPX1|]. rewrite <- HS1.
      eapply presA_weaken; [exact HP| intros b Hb; apply in_or_app; right; exact (xa_keep_sub _ _ _ _ _ _ _ _ J Hb)| intros b Hb; exact Hb
                           | clear - FS16; lia| clear; lia| clear; lia| intros y _; exact I].
    - eapply aobj_cs_mono; [exact HCS2|].
      eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hc)| exact HP| exact OX1| intros x Hx; eapply hcs_below_top; exact Hx|].
      right. split; [eapply xa_crX; [exact J| clear - FS16; lia]| clear - ALO LOS LOSP; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_calloc_fail : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Pdv,$<.Pdf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.Pm2,P,(11.&40.)(17.(11.&8.))Ph2,(16.Vsegs,VR,VHIA,)P,(19.(28.$15.)R:.R9.R6.R5.R4.R3.)P,(3:.Vsegs,R3.)P,(3;.Vsegs,R4.Vlo,(2.(3.&40.Vsp,)VFS,))P,(44.Vsegs,VR,R8.VLF,(2.(3.&40.Vsp,)VFS,)(8.VR,)(45.Vsegs,VR,VHIA,R9.)(28.$3?.)R7.R5.)P,(;.$<.(36.Vsegs,VR,VHIA,R5.)(36.Vsegs,VR,VHIA,R:.))P,(;.$<.(45.Vsegs,VR,VHIA,R6.)(45.Vsegs,VR,VHIA,R;.))P,(;.$<.(46.Vsegs,VR,VHIA,R7.)(46.Vsegs,VR,VHIA,R<.))P,Px,$<.P,(33.Vsegs,VR,VHIA,R>.R1.)(33.Vsegs,VR,VHIA,R:.R2.)P,(1.(47.Vsegs,VR,VHIA,R9.)(:.(47.Vsegs,VR,VHIA,R>.)R10.))P,(1.(48.Vsegs,VR,VHIA,R:.)(:.(48.Vsegs,VR,VHIA,R?.)R10.))P,(39.Vsegs,VR,VHIA,R;.R?.VLF,R<.)(19.(28.$15.)(:.R15.R13.)(:.R14.R12.)R<.R10.R=.R>.)")
(* [comment removed for export] *).
  Proof. intros. eapply (xa_transport [] []); eassumption. Qed.

  (* [comment removed for export] *)
  Record FBA (LBc : list blk) (An cnt : Z) (ys : list word) (mc : mem) (dXc : mpd) : Prop := {
    fb_fresh : fresh_apart R LBc LF An (4 * cnt);
    fb_fresh0 : fresh_apart R (mpd_keep LB dX) LF An (4 * cnt);
    fb_al : An mod 16 = 0;
    fb_new : ~ In (An, 4 * cnt) LB;
    fb_newc : ~ In (An, 4 * cnt) LBc;
    fb_apart : forall B k, In (B, k) (LBc ++ fdata LF) -> An + 4 * cnt <= B \/ B + k <= An;
    fb_arr : u32arr segs mc An ys;
    fb_len : Z.of_nat (length ys) = cnt;
    fb_cnt : 0 <= md_n dXc < cnt /\ cnt <= 10000;
    fb_XS : X + 16 <= An \/ An + 4 * cnt <= X;
    fb_lo : An + 4 * cnt <= lo
  }.

  #[using="JC"] Lemma xa_calloc_ok : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Pdv,$<.Pdf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.Pm2,P,(11.&40.)(17.(11.&8.))Ph2,(16.Vsegs,VR,VHIA,)PAn,$<.Pcnt,$<.P,(19.(28.$15.)R<.R;.R8.R7.R6.R5.)P,(3:.Vsegs,R5.)P,(3;.Vsegs,R6.Vlo,(2.(3.&40.Vsp,)VFS,))P,(44.Vsegs,VR,R:.VLF,(2.(3.&40.Vsp,)VFS,)(8.VR,)(45.Vsegs,VR,VHIA,R;.)(28.$3?.)R9.R7.)P,(;.$<.(36.Vsegs,VR,VHIA,R7.)(36.Vsegs,VR,VHIA,R<.))P,(;.$<.(45.Vsegs,VR,VHIA,R8.)(45.Vsegs,VR,VHIA,R=.))P,(;.$<.(46.Vsegs,VR,VHIA,R9.)(46.Vsegs,VR,VHIA,R>.))P,Px,$<.P,(33.Vsegs,VR,VHIA,R10.R1.)(33.Vsegs,VR,VHIA,R<.R2.)P,(1.(47.Vsegs,VR,VHIA,R;.)(:.(47.Vsegs,VR,VHIA,R10.)R12.))P,(1.(48.Vsegs,VR,VHIA,R<.)(:.(48.Vsegs,VR,VHIA,R11.)R12.))P,(39.Vsegs,VR,VHIA,R=.(3=.(1<.$<.$<.)(2<.$<.$<.R<.(2=.+4.R;.))R11.)VLF,R>.)P,(;.$<.(=.R=.+10.)=)P,(49.VR,R13.VLF,R>.(2=.+4.R=.))P,(20.Vsegs,R11.R?.(3=.$4:.(4;.(4<.(2=.+4.R>.))(4=.(11.&8.)(23.&8.=)(4<.(2=.+4.R>.))))(28.$4:.)))P,(0.(4.(13.R13.)R?.)(1.R?.+2710.))(0.(19.(3=.(1<.$<.$<.)(2<.$<.$<.R11.(2=.+4.R10.))(28.(1<.$<.$<.)))(:.R1;.R19.)(:.R1:.R18.)R12.R16.R13.R14.)(4>.R16.R11.R10.(4=.(11.&40.)(23.&40.=)(4<.R10.))R13.R14.))")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f dv df hc LBc mc dXc m2 h2 An cnt J MI2 ST2 HP HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW CNT.
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    assert (J2 : XJA [(An, 4 * cnt)] (v + dv) (f + df) h2 LBc m2 dXc) by (eapply (xa_transport [] [(An, 4 * cnt)]); eassumption).
    split; [exact J2|].
    dpose HFRA as (A0 & AC & AD & HAP).
    assert (NEWC : ~ In (An, 4 * cnt) LBc) by (intros Hin; destruct (HAP An (4 * cnt) ltac:(apply in_or_app; left; exact Hin)); clear - H CNT NR1; lia).
    constructor.
    - exact HFRA.
    - pose proof HFRA as HF'. ddestruct HF' as (B0 & BC & BD & BAP). split; [exact B0|]. split; [exact BC|]. split; [exact BD|].
      intros B j Hb. apply BAP. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (xa_keep_sub _ _ _ _ _ _ _ _ J Hb)| right; exact Hb].
    - exact A16.
    - intros Hin. destruct (xa_blocks_orig _ _ _ _ _ _ _ _ J Hin) as [C|C]; [exact (NEWC C)|].
      unfold mpd_blk in C. destruct (md_own dX) eqn:EO; try (destruct C; fail). destruct C as [E|[]].
      pose proof MX as [(_ & _ & _ & _ & _ & OWd) _]. rewrite EO in OWd. destruct OWd as (Nd & _).
      injection E as E1 E2. pose proof (xa_nmono _ _ _ _ _ _ _ J) as NM1. clear - E2 Nd NM1 CNT. lia.
    - exact NEWC.
    - exact HAP.
    - eapply u32arr_of_cells; [exact HNEW|]. rewrite u32s_repeat0. f_equal. clear - CNT NR1; lia.
    - rewrite repeat_length. clear - CNT NR1; lia.
    - clear - CNT NR1; lia.
    - destruct (fresh_apart_client R LBc LF (SP - FS) X 16 An (4 * cnt) HFRA); [| clear; lia| clear - CNT NR1; lia| clear - ALO LOS LOSP; lia| right; assumption| left; assumption].
      eapply client_range_inside; [eapply client_wrange_sp_mono; [| exact (xa_cwX _ _ _ _ _ _ _ J)]; clear - FS16; lia| intros b Hb; exact Hb| clear; lia| clear; lia].
    - clear - AC ALO LOS. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fba_munch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PLBc,(14.$15.)PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PW,(14.$3?.)Pm',P,(11.&40.)(17.(11.&8.))P,(4>.R8.R7.R6.R5.R4.R3.)P,(3<.R3.R5.R2.)P,(3>.Vsegs,R6.R3.)P,(41.R5.R:.(2=.+4.R9.))(4>.R<.R;.R:.R9.R5.R7.)")
(* [comment removed for export] *).
  Proof.
    intros LBc An cnt ys mc dXc W m' [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11] MU WM DJ. constructor; try assumption.
    eapply (u32arr_transport segs W mc m'); [exact F7| exact MU| exact WM|].
    replace (4 * Z.of_nat (length ys)) with (4 * cnt) by (clear - F8; lia). exact DJ.
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xga_memcpy_pre : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))P,(19.(3=.(1<.$<.$<.)(2<.$<.$<.R3.(2=.+4.R2.))(28.(1<.$<.$<.)))R9.R8.R7.R6.R5.R4.)P,(4>.R7.R4.R3.R2.R6.R5.)P,(;.$25.(26.R6.)$2:.)(0.(4?.Vsegs,R8.(22.R7.)(50.(12.R7.)))(0.(;.$42.(10.(11.&8.)(50.(12.R7.)))(4<.(2=.+4.(13.R7.))))(0.(20.Vsegs,R8.R6.(3=.$4:.(4;.(51.#4.(10.(11.&40.)(52.(11.&40.)(4<.(13.R7.))R4.)))(50.(52.(11.&40.)(4<.(13.R7.))R4.)))(28.$4:.)))(0.(;.$42.(51.#4.(10.(11.&40.)(52.(11.&40.)(4<.(13.R7.))R4.)))(4<.(2=.+4.(13.R7.))))(0.(>.(1.(:.(22.R7.)(2=.+4.(13.R7.)))R6.)(1.(:.R6.(2=.+4.(13.R7.)))(22.R7.)))(0.(4.=(22.R7.))(0.(1.(:.(22.R7.)(2=.+4.(13.R7.)))(6.(7.VR,)))(0.(4.=R6.)(0.(1.(:.R6.(2=.+4.R5.))(6.(7.VR,)))(0.(31.Vsegs,(32.VR,)(33.Vsegs,VR,VHIA,R:.)R8.R6.(2=.+4.R5.))(0.(31.Vsegs,(32.VR,)(33.Vsegs,VR,VHIA,R:.)R8.(22.R7.)(2=.+4.(13.R7.)))(0.(1.(:.(:.(22.R7.)(2=.+4.(13.R7.)))+8.)(5.+2.+2?.))(0.(1.(:.(:.R6.(2=.+4.R5.))+8.)(5.+2.+2?.))(0.(2;.(1<.$<.$<.)(2<.$<.$<.R6.(2=.+4.R5.))(1>.(1<.$<.$<.)(3=.(1<.$<.$<.)(2<.$<.$<.R6.(2=.+4.R5.))(28.(1<.$<.$<.)))R9.))(2;.(1<.$<.$<.)(2<.$<.$<.(22.R7.)(2=.+4.(13.R7.)))(1>.(1<.$<.$<.)(3=.(1<.$<.$<.)(2<.$<.$<.R6.(2=.+4.R5.))(28.(1<.$<.$<.)))R9.))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros v f hc LBc mc dXc An cnt ys J F EO.
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
    pose proof F as [FR FR0 A16 NEW NEWC APA ARR LENY CNT FXS ALO']. dpose FR as (An0 & AnC & AnD & HAP).
    split; [apply u32arr_ro; exact XARR|]. split; [rewrite u32s_length; clear - LEN1 NR1; lia|].
    rewrite <- (firstn_skipn (Z.to_nat (md_n dXc)) ys) in ARR. apply u32arr_app in ARR. destruct ARR as [A1 A2].
    split; [apply u32arr_cells; exact A1|].
    assert (LF' : length (firstn (Z.to_nat (md_n dXc)) ys) = Z.to_nat (md_n dXc)) by (rewrite firstn_length; clear - LENY CNT NR1; lia).
    split; [rewrite LF'; clear - NR1; lia|]. split; [destruct (APA _ _ ltac:(apply in_or_app; left; exact XIN)); clear - H CNT; lia|].
    split; [exact P0|]. split; [exact PC|]. split; [exact An0|]. split; [exact AnC|].
    split; [eapply hm_aobj_block; [exact (xa_hm _ _ _ _ _ _ _ J)| left; reflexivity]|]. split; [exact OP|]. split; [exact P47|].
    split; [eapply blk_top47; [exact (xa_hm _ _ _ _ _ _ _ J)| left; reflexivity]|].
    split; [left; reflexivity| right; exact XIN].
  Qed.

  #[using="JC"] Lemma xga_memcpy_post : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))Pm3,P,(11.&40.)(17.(11.&8.))P,(19.(3=.(1<.$<.$<.)(2<.$<.$<.R4.(2=.+4.R3.))(28.(1<.$<.$<.)))R:.R9.R8.R7.R6.R5.)P,(4>.R8.R5.R4.R3.R7.R6.)P,(;.$25.(26.R7.)$2:.)P,(3<.(3=.(1<.$<.$<.)(2<.$<.$<.R7.(:.R7.(2=.+4.(13.R8.))))(3=.(1<.$<.$<.)(2<.$<.$<.Vlo,(2.(3.&40.Vsp,)VFS,))(28.(1<.$<.$<.))))R9.R4.)P,(3>.Vsegs,R:.R5.)P,(3:.Vsegs,R6.)P,(3;.Vsegs,R7.Vlo,(2.(3.&40.Vsp,)VFS,))P,(20.Vsegs,R8.R;.(3=.$4:.(4;.(4<.(2=.+4.(13.R<.)))(50.(12.R<.)))(28.$4:.)))P,(39.Vsegs,VR,VHIA,R10.(3=.(1<.$<.$<.)(2<.$<.$<.R<.(2=.+4.R;.))R?.)VLF,R9.)P,(31.Vsegs,(32.VR,)(33.Vsegs,VR,VHIA,R11.)R:.(9.VdX,)+10.)(0.(19.(3=.(1<.$<.$<.)(2<.$<.$<.R>.(2=.+4.R=.))(28.(1<.$<.$<.)))R14.R13.R12.R11.R;.R?.)(4>.R11.R>.R=.(1>.(11.&40.)(12.R?.)(53.(11.&40.)(4<.(13.R?.))R<.))R;.R?.))")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f hc LBc mc dXc An cnt ys m3 J F EO MU WM MI3 ST3 CP HH3 OX3.
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
    pose proof F as [FRn FR0 A16 NEW NEWC APA ARR LENY CNT FXS ALO']. dpose FRn as (An0 & AnC & AnD & HAP).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    pose proof (XLS1 ltac:(rewrite EO; discriminate)) as XLSc.
    pose proof (hm_top segs R HIA h LB LF m HH) as HTOP0.
    assert (SCSc : crange (hcs segs R HIA hc) lo (SP - FS - lo)).
    { eapply crange_sub; [exact (hcs_stack segs R HIA hc)| exact LOS| rewrite HS1; clear - HTOP0 TOP FS16; lia]. }
    split.
    - constructor; try assumption.
      + eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. cbn. rewrite FSZ. clear - ALO' CNT LOSP; lia.
      + eapply mpd_at_munch_any; [exact MX1| exact MU| exact WM| rewrite AD1; cbn; clear - FXS CNT DSX FS16; lia|].
        intros _. cbn. destruct (APA _ _ ltac:(apply in_or_app; left; exact XIN)); clear - H CNT XLSc FS16; lia.
      + eapply presA_trans; [exact HPX1|]. rewrite <- HS1.
        eapply (presA_drop_fresh segs R HIA hc (mpd_keep LB dX) LF [(X, X + 16)] An (4 * md_n dXc) mc m3 SP);
          [| eapply fresh_apart_sub; [exact FR0| clear - CNT; lia]| clear - LOS LOSP FS16; lia].
        eapply (presA_weaken segs R ([(An, 4 * cnt)] ++ LBc) (mpd_keep LB dX) LF LF SP SP (arl_stklo R) (arl_stklo R)
                  (hstkhi segs R HIA hc) (hstkhi segs R HIA hc) ((An, An + 4 * md_n dXc) :: [(X, X + 16)]));
          [| intros b Hb; apply in_or_app; right; exact (xa_keep_sub _ _ _ _ _ _ _ _ J Hb)| intros b Hb; exact Hb
           | clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
        eapply (presA_drop_below segs R HIA hc ([(An, 4 * cnt)] ++ LBc) LF _ lo (SP - FS) mc mc m3 SP); [exact HH1| | clear - LOSP FS16; lia| exact LOS].
        eapply (presA_of_munch segs R ([(An, 4 * cnt)] ++ LBc) LF _ _ _ _ mc m3 (hcs segs R HIA hc) (hcs_ok segs R HIA hc)); [| | | exact WM].
        * unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (SP - FS - lo)) with (SP - FS) by (clear; lia); exact SCSc|].
          apply Forall_cons; [cbn [fst snd]; replace (An + 4 * md_n dXc - An) with (4 * md_n dXc) by (clear; lia);
                              eapply aobj_crange; eapply aobj_sub; [eapply hm_aobj_block; [exact HH1| left; reflexivity]| clear; lia| clear - CNT; lia]|].
          apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX1| apply Forall_nil].
        * intros c0 Hc. eapply cshd_hcs; [exact HH1| | exact Hc]. clear; lia.
        * eapply munch_weaken; [| exact MU]. intros a Ha. cbn [outside fst snd] in Ha |- *. clear - Ha. tauto.
    - constructor; try assumption.
      + rewrite <- (firstn_skipn (Z.to_nat (md_n dXc)) ys) in ARR. apply u32arr_app in ARR. destruct ARR as [_ A2].
        rewrite firstn_length in A2. replace (Init.Nat.min (Z.to_nat (md_n dXc)) (length ys)) with (Z.to_nat (md_n dXc)) in A2 by (clear - LENY CNT NR1; lia).
        apply u32arr_app. split; [eapply u32arr_of_cells; [exact CP| reflexivity]|].
        replace (4 * Z.of_nat (length (md_limbs dXc))) with (4 * Z.of_nat (Z.to_nat (md_n dXc))) by (clear - LEN1 NR1; lia).
        eapply u32arr_transport; [exact A2| exact MU| exact WM|]. cbn. rewrite skipn_length. clear - LENY CNT NR1 ALO' LOSP; lia.
      + rewrite app_length, skipn_length. clear - LENY LEN1 CNT NR1; lia.
  Qed.

  (* [comment removed for export] *)
  Record XDA (v f : Z) (hd : HST segs R HIA) (LBd : list blk) (An cnt : Z) (ys : list word) (me : mem) (dXc : mpd) : Prop := {
    xd_mi : mem_inv segs me;
    xd_stk : stk segs me lo (SP - FS);
    xd_fr : rw_cells segs me (SP - FS) FRAME;
    xd_hm : HM segs R HIA hd ((An, 4 * cnt) :: LBd) LF me;
    xd_top : htop segs R HIA hd = htop segs R HIA h;
    xd_stkhi : hstkhi segs R HIA hd = hstkhi segs R HIA h;
    xd_flag : hflag segs R HIA hd = hflag segs R HIA h;
    xd_hcs : forall x, hcs segs R HIA h x -> hcs segs R HIA hd x;
    xd_vol : havol segs R HIA hd <= havol segs R HIA h + v;
    xd_frs : hfr segs R HIA hd <= hfr segs R HIA h + f;
    xd_struct : rw_cells segs me X (mpi_cells (md_p dXc) (Z_to_bv 64 (md_sg dXc)) (md_n dXc) (md_pad dX));
    xd_sg : md_sg dXc = 1 \/ md_sg dXc = -1;
    xd_sub : forall b, In b LBd -> In b LB;
    xd_keep : forall b, In b LB -> ~ In b (mpd_blk dX) -> In b LBd;
    xd_gone : forall b, In b (mpd_blk dX) -> ~ In b LBd;
    xd_new : ~ In (An, 4 * cnt) LB;
    xd_apart : forall B k, In (B, k) (LBd ++ fdata LF) -> An + 4 * cnt <= B \/ B + k <= An;
    xd_arr : u32arr segs me An ys;
    xd_len : Z.of_nat (length ys) = cnt;
    xd_cnt : 0 <= md_n dXc < cnt /\ cnt <= 10000;
    xd_XS : X + 16 <= An \/ An + 4 * cnt <= X;
    xd_pres : presA segs R (mpd_keep LB dX) LF SP (arl_stklo R) (hstkhi segs R HIA h) [(X, X + 16)] m me;
    xd_fresh0 : fresh_apart R (mpd_keep LB dX) LF An (4 * cnt);
    xd_al : An mod 16 = 0;
    xd_aobjX : aobj segs AL (hcs segs R HIA hd) me X 16;
    xd_lo : An + 4 * cnt <= lo;
    xd_nmono : md_n dX <= md_n dXc
  }.

  #[using="JC"] Lemma xga_null : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))P,(19.(3=.(1<.$<.$<.)(2<.$<.$<.R3.(2=.+4.R2.))(28.(1<.$<.$<.)))R9.R8.R7.R6.R5.R4.)P,(4>.R7.R4.R3.R2.R6.R5.)P,(;.$25.(26.R6.)$27.)(54.R<.R;.R:.R9.R6.R5.R4.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros v f hc LBc mc dXc An cnt ys J F EO.
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    pose proof F as [FRn FR0 A16 NEW NEWC APA ARR LENY CNT FXS ALO'].
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    dpose OUT1 as (_ & _ & O3 & O4 & O5).
    constructor; try assumption.
    - intros b Hb. destruct (O3 b Hb) as [C|C]; [exact C|]. unfold mpd_blk in C. rewrite EO in C. destruct C.
    - intros b HbX HbC. pose proof (O5 b HbX HbC) as E. unfold mpd_blk in E, HbX. rewrite EO in E.
      destruct (md_own dX); try (destruct HbX; fail). discriminate.
  Qed.

  #[using="JC"] Lemma xga_zfree_pre : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))P,(19.(3=.(1<.$<.$<.)(2<.$<.$<.R3.(2=.+4.R2.))(28.(1<.$<.$<.)))R9.R8.R7.R6.R5.R4.)P,(4>.R7.R4.R3.R2.R6.R5.)P,(;.$25.(26.R6.)$2:.)(0.(2;.(1<.$<.$<.)(2<.$<.$<.(22.R7.)(2=.+4.(13.R7.)))(3=.(1<.$<.$<.)(2<.$<.$<.R6.(2=.+4.R5.))R9.))(0.(20.Vsegs,R8.(22.R7.)(3=.$4:.(4;.(51.#4.(10.(11.&40.)(12.R7.)))(50.(12.R7.)))(28.$4:.)))(0.(;.$42.(51.#4.(10.(11.&40.)(12.R7.)))(4<.(2=.+4.(13.R7.))))(0.(0.(1.=(2=.+4.(13.R7.)))(4.(2=.+4.(13.R7.))(5.+2.+40.)))(1.+1.(13.R7.))))))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros v f hc LBc mc dXc An cnt ys J F EO.
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
    split; [right; exact XIN|]. split; [apply u32arr_cells; exact XARR|]. clear - LEN1 NR1 N1. lia.
  Qed.

  #[using="JC"] Lemma xga_zfree_post : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Pdv,$<.Pdf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))Pm4,P,(11.&40.)(17.(11.&8.))Ph4,(16.Vsegs,VR,VHIA,)P,(19.(3=.(1<.$<.$<.)(2<.$<.$<.R5.(2=.+4.R4.))(28.(1<.$<.$<.)))R=.R<.R9.R8.R7.R6.)P,(4>.R9.R6.R5.R4.R8.R7.)P,(;.$25.(26.R8.)$2:.)P,(3:.Vsegs,R5.)P,(3;.Vsegs,R6.Vlo,(2.(3.&40.Vsp,)VFS,))P,(44.Vsegs,VR,(55.(22.R;.)(3=.(1<.$<.$<.)(2<.$<.$<.R:.(2=.+4.R9.))R=.))VLF,(2.(3.&40.Vsp,)VFS,)(8.VR,)(45.Vsegs,VR,VHIA,R>.)(3=.(1<.$<.$<.)(2<.$<.$<.(22.R;.)(:.(22.R;.)(2=.+4.(13.R;.))))(28.(1<.$<.$<.)))R<.R7.)P,(;.$<.(36.Vsegs,VR,VHIA,R7.)(36.Vsegs,VR,VHIA,R?.))P,(;.$<.(45.Vsegs,VR,VHIA,R8.)(45.Vsegs,VR,VHIA,R10.))P,(;.$<.(46.Vsegs,VR,VHIA,R9.)(46.Vsegs,VR,VHIA,R11.))P,Px,$<.P,(33.Vsegs,VR,VHIA,R13.R1.)(33.Vsegs,VR,VHIA,R<.R2.)P,(1.(47.Vsegs,VR,VHIA,R;.)(:.(47.Vsegs,VR,VHIA,R13.)R15.))P,(1.(48.Vsegs,VR,VHIA,R<.)(:.(48.Vsegs,VR,VHIA,R14.)R15.))P,(39.Vsegs,VR,VHIA,R=.(55.(22.R12.)(3=.(1<.$<.$<.)(2<.$<.$<.R11.(2=.+4.R10.))R14.))VLF,R>.)(54.(:.R1:.R18.)(:.R19.R17.)R>.(55.(22.R13.)R15.)R12.R11.R10.R?.R13.)")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f dv df hc LBc mc dXc An cnt ys m4 h4 J F EO MI4 ST4 HP4 HT4 HS4 HF4 HCS4 HV4 HFR4 HH4.
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
    pose proof F as [FRn FR0 A16 NEW NEWC APA ARR LENY CNT FXS ALO']. dpose FRn as (An0 & AnC & AnD & HAP).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    dpose OUT1 as (_ & _ & O3 & O4 & O5).
    assert (NEA : An <> md_p dXc) by (destruct (APA _ _ ltac:(apply in_or_app; left; exact XIN)); clear - H CNT N1; lia).
    pose proof (lb_remove_cons_other An (4 * cnt) (md_p dXc) LBc NEA) as ELB. rewrite ELB in HH4. rewrite ELB in HP4.
    assert (NDc : List.NoDup (map fst LBc)) by (cbn in ND1; inversion ND1; assumption).
    assert (NOTIN : ~ In (md_p dXc, 4 * md_n dXc) (lb_remove (md_p dXc) LBc)) by (apply lb_remove_notin; exact NDc).
    assert (KEEPc : forall q k, In (q, k) LBc -> (q, k) <> (md_p dXc, 4 * md_n dXc) -> In (q, k) (lb_remove (md_p dXc) LBc)).
    { intros q k Hq NE. eapply in_lb_remove_other; [exact NDc| exact XIN| exact Hq| exact NE]. }
    (* [comment removed for export] *)
    assert (HP4' : presA segs R ((An, 4 * cnt) :: lb_remove (md_p dXc) LBc) LF (SP - FS) (arl_stklo R) (hstkhi segs R HIA hc) [] mc m4).
    { eapply (presA_drop_freed segs R HIA hc ((An, 4 * cnt) :: LBc) LF _ [] (md_p dXc) (4 * md_n dXc) mc mc m4);
        [exact HH1| right; exact XIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS LOSP; lia| ].
      - intros b xb [Hb|Hb] Hr.
        + subst b. split; [left; reflexivity|]. intros E. injection E as E1 E2. exact (NEA E1).
        + split; [right; eapply In_lb_remove; exact Hb|]. intros E. subst b. exact (NOTIN Hb).
      - exact HP4. }
    constructor; try assumption.
    - eapply (presA_rw_cells segs R); [exact HP4'| exact FR1| rewrite FSZ; apply client_range_stack; clear; lia| cbn; exact I].
    - rewrite HT4; exact HT1.
    - rewrite HS4; exact HS1.
    - rewrite HF4; exact HF1.
    - intros x Hx; apply HCS4, HCS1, Hx.
    - clear - HV1 HV4; lia.
    - clear - HFR1 HFR4; lia.
    - eapply (presA_rw_cells segs R); [exact HP4'| exact CX1| | cbn; exact I].
      unfold mpi_cells; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      intros a Ha. destruct (xa_cwX _ _ _ _ _ _ _ J a Ha) as [C|[C|([q k] & Hq & Rq)]]; [left; clear - C FS16; lia| right; left; exact C| right; right].
      exists (q, k). split; [| exact Rq]. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left| right; exact Hq].
      right. apply KEEPc; [exact Hq|]. intros E. injection E as -> ->. cbn in Rq, Ha. pose proof (XP1 EO). clear - Rq Ha H. lia.
    - intros b Hb. pose proof (In_lb_remove _ _ _ Hb) as HbC. destruct (O3 b HbC) as [C|C]; [exact C|].
      unfold mpd_blk in C. rewrite EO in C. destruct C as [<-|[]]. exfalso. exact (NOTIN Hb).
    - intros [q k] Hb NX. pose proof (O4 _ Hb NX) as HbC. apply KEEPc; [exact HbC|]. intros E. rewrite E in *.
      destruct (FRS1 (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [C|C]; [exact (NX C)| exact (C Hb)].
    - intros b HbX Hb4. pose proof (In_lb_remove _ _ _ Hb4) as HbC. pose proof (O5 b HbX HbC) as E.
      assert (Hb' : In b (mpd_blk dXc)) by (rewrite E; exact HbX). unfold mpd_blk in Hb'. rewrite EO in Hb'. destruct Hb' as [<-|[]]. exact (NOTIN Hb4).
    - intros q k Hq. apply APA. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left; eapply In_lb_remove; exact Hq| right; exact Hq].
    - destruct ARR as [AB AW]. split.
      + eapply heap_presx_bytes_at; [exact (presA_presx segs R _ _ _ _ _ _ _ _ HP4')| exact AB| rewrite u32s_length; eapply client_range_block; [apply in_or_app; left; left; reflexivity| clear; lia| clear - LENY; lia]| cbn; exact I].
      + eapply heap_presx_wr_at; [exact (presA_presx segs R _ _ _ _ _ _ _ _ HP4')| exact AW| eapply client_range_block; [apply in_or_app; left; left; reflexivity| clear; lia| clear - LENY; lia]| cbn; exact I].
    - eapply presA_trans; [exact HPX1|]. rewrite <- HS1.
      eapply presA_weaken; [exact HP4'| | intros b Hb; exact Hb| clear - FS16; lia| clear; lia| clear; lia| intros y _; exact I].
      intros [q k] Hb. right. apply KEEPc; [exact (xa_keep_sub _ _ _ _ _ _ _ _ J Hb)|].
      intros E. injection E as -> ->.
      destruct (FRS1 (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [C|C].
      + unfold mpd_keep in Hb. unfold mpd_blk in C. destruct (md_own dX); try (destruct C; fail). destruct C as [E|[]].
        apply filter_In in Hb. destruct Hb as [_ Hne]. rewrite <- E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
      + exact (C (In_mpd_keep _ _ _ Hb)).
    - eapply aobj_cs_mono; [exact HCS4|].
      eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hc)| exact HP4'| exact OX1| intros x Hx; eapply hcs_below_top; exact Hx|].
      right. split; [| clear - ALO LOS LOSP; lia].
      intros a Ha. destruct (xa_cwX _ _ _ _ _ _ _ J a Ha) as [C|[C|([q k] & Hq & Rq)]]; [left; clear - C FS16; lia| right; left; exact C| right; right].
      exists (q, k). split; [| exact Rq]. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left| right; exact Hq].
      right. apply KEEPc; [exact Hq|]. intros E. injection E as -> ->. cbn in Rq, Ha. pose proof (XP1 EO). clear - Rq Ha H. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xda_finish : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phd,(16.Vsegs,VR,VHIA,)PLBd,(14.$15.)PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))Pme,P,(11.&40.)(17.(11.&8.))PdXc,$18.Pm5,P,(11.&40.)(17.(11.&8.))P,(54.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(3<.(3=.(1<.$<.$<.)(2<.$<.$<.(9.VdX,)(:.(9.VdX,)+10.))(28.(1<.$<.$<.)))R4.R2.)P,(3>.Vsegs,R5.R3.)P,(3:.Vsegs,R4.)P,(20.Vsegs,R5.(9.VdX,)(21.R:.(23.&40.(1?.R6.))R9.(24.VdX,)))P,(39.Vsegs,VR,VHIA,R=.(3=.(1<.$<.$<.)(2<.$<.$<.R;.(2=.+4.R:.))R<.)VLF,R6.)P,(31.Vsegs,(32.VR,)(33.Vsegs,VR,VHIA,R>.)R7.(9.VdX,)+10.)(19.(28.$15.)R11.R10.R?.(3=.(1<.$<.$<.)(2<.$<.$<.R=.(2=.+4.R<.))R>.)R8.(43.(9.VdX,)(1?.R9.)R<.R=.R;.(24.VdX,)$2:.))")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f hd LBd An cnt ys me dXc m5 D MU WM MI5 CX5 HH5 OX5.
    pose proof D as [MI4 ST4 FR4 HH4 HT4 HS4 HF4 HCS4 HV4 HFR4 CX4 SG SUB KEEP GONE NEW APA ARR LENY CNT DXS HPX4 FR0 A16 OX4 ALO' NMX].
    assert (KSUB : forall b, In b (mpd_keep LB dX) -> In b ((An, 4 * cnt) :: LBd)).
    { intros b Hb. right. apply KEEP; [eapply In_mpd_keep; exact Hb|].
      unfold mpd_keep in Hb. unfold mpd_blk. destruct (md_own dX); try (intros []; fail).
      apply filter_In in Hb. destruct Hb as [_ Hne]. intros [E|[]]. rewrite <- E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne. }
    constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption; try reflexivity.
    - eapply stk_transport_disjoint; [exact ST4| exact MU| exact WM|]. cbn. clear - DSX LOSP FS16; lia.
    - eapply rw_cells_transport; [exact FR4| exact MU| exact WM|]. cbn. rewrite FSZ. clear - DSX LOSP; lia.
    - split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CX5|]. split; [exact XAL|]. split; [exact X0|]. split; [exact LENY|]. split; [unfold MPI_MAX_LIMBS; clear - CNT; lia|].
      split; [clear - CNT; lia|]. split; [left; reflexivity|]. split; [exact A16|].
      eapply u32arr_transport; [exact ARR| exact MU| exact WM|]. cbn. clear - DXS CNT LENY; lia.
    - discriminate.
    - unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
      split; [intros b [<-|Hb]; [right; left; reflexivity| left; exact (SUB b Hb)]|].
      split; [intros b Hb NX; right; exact (KEEP b Hb NX)|].
      intros b HbX [<-|Hb4]; [exfalso| exfalso; exact (GONE b HbX Hb4)].
      apply NEW. unfold mpd_blk in HbX. pose proof MX as [(_ & _ & _ & _ & _ & OWd) _]. destruct (md_own dX); try (destruct HbX; fail).
      destruct HbX as [E|[]]. rewrite <- E. exact (proj1 (proj2 OWd)).
    - unfold mpd_blk; cbn [md_own md_p md_n]. intros b [<-|[]]. right. exact NEW.
    - unfold mpd_blk; cbn [md_own md_p md_n]. intros b [<-|[]]. right. cbn [fst snd]. exact FR0.
    - eapply presA_trans; [exact HPX4|]. rewrite <- HS4.
      eapply (presA_of_munch segs R (mpd_keep LB dX) LF _ _ _ _ me m5 (hcs segs R HIA hd) (hcs_ok segs R HIA hd)); [| | exact MU| exact WM].
      + unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (X + 16 - X) with 16 by (clear; lia). eapply aobj_crange. exact OX4.
      + intros c0 Hc. eapply cshd_hcs; [exact HH4| | eapply cshd_mono_lb; [exact Hc| exact KSUB]]. clear; lia.
    - intros _. exact DXS.
    - intros _. left. exact ALO'.
    - clear - NMX CNT. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xda_cwX : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phd,(16.Vsegs,VR,VHIA,)PLBd,(14.$15.)PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))Pme,P,(11.&40.)(17.(11.&8.))PdXc,$18.P,(54.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(34.(7.VR,)(1>.(1<.$<.$<.)(3=.(1<.$<.$<.)(2<.$<.$<.R6.(2=.+4.R5.))R7.)(35.VLF,))(3.&40.Vsp,)(36.Vsegs,VR,VHIA,Vh,)(9.VdX,)+10.)")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros v f hd LBd An cnt ys me dXc D. destruct XW as [XCW XP].
    eapply client_wrange_mono; [exact (client_wrange_keep L LB LF _ _ dX X 16 XCW XP)|].
    intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
    right. apply (xd_keep _ _ _ _ _ _ _ _ _ D); [eapply In_mpd_keep; exact Hb|].
    unfold mpd_keep in Hb. unfold mpd_blk. destruct (md_own dX); try (intros []; fail).
    apply filter_In in Hb. destruct Hb as [_ Hne]. intros [E|[]]. rewrite <- E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_post : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PRr,P,$<.P,$18.SpPPHI,$<.PFR,$<.Pr,$<.Pmo,$56.Pmo9,$56.Pra,(11.&40.)Pgp,(11.&40.)Ptp,(11.&40.)Pt0,(11.&40.)Pt1,(11.&40.)Pt2,(11.&40.)Ps0,(11.&40.)Ps1,(11.&40.)Pa1,(11.&40.)Pa2,(11.&40.)Pa3,(11.&40.)Pa4,(11.&40.)Pa5,(11.&40.)Pa6,(11.&40.)Pa7,(11.&40.)Ps2,(11.&40.)Ps3,(11.&40.)Ps4,(11.&40.)Ps5,(11.&40.)Ps6,(11.&40.)Ps7,(11.&40.)Ps8,(11.&40.)Ps9,(11.&40.)Ps10,(11.&40.)Ps11,(11.&40.)Pt3,(11.&40.)Pt4,(11.&40.)Pt5,(11.&40.)Pt6,(11.&40.)PF,(57.&5.(11.&40.))Pfc,(11.&20.)P,(19.(28.$15.)R2;.R2:.R29.R28.R27.R26.)P,A2.R26.R23.R27.P,(58.Vsegs,VR,VHIA,R2;.R22.)P,(59.R24.R23.)P,(1.R2?.R28.)P,(1.R2?.R28.)(5:.Vsegs,VR,VHIA,R25.Vsp,R24.R23.R1?.R1>.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R8.R7.Vh,VLB,VLF,VdX,R2;.R2:.R29.Vlo,Vm,R27.(5;.(5<.(5=.R25.Vsp,R24.R23.R22.R21.R20.R1?.R1>.(23.&40.R28.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R8.(5>.R25.)R7.(5?.(11.&40.))R2=.(60.Vsegs,))R26.))")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros until fc. intros J HR HK9 MF9 HV HF.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    unfold mpi_binop_postA. deexists 14. dexists mc, mo9, hc, LBc, dXc, r.
    split; [reflexivity|]. split; [exact MI1|].
    split; [pose proof (stk_release segs mc lo (SP - FS) FRAME ST1 FR1 ltac:(clear - LOSP LO0; lia)) as ST; rewrite FSZ in ST; replace (SP - FS + FS) with SP in ST by (clear; lia); exact ST|].
    split; [exact MF9|]. split; [exact HPX1|]. split; [exact HT1|]. split; [exact HS1|]. split; [exact HF1|]. split; [exact HK9|]. split; [exact HCS1|].
    split; [clear - HV1 HV; lia|]. split; [clear - HFR1 HF; lia|]. split; [exact HH1|]. split; [exact MX1|]. split; [exact OUT1|]. split; [exact FRA1| exact HR].
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_struct_sign : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.Pm',P,(11.&40.)(17.(11.&8.))Psg',$<.P,(19.(28.$15.)R8.R7.R6.R5.R4.R3.)P,(3<.(3=.(1<.$<.$<.)(2<.$<.$<.(9.VdX,)(:.(9.VdX,)+10.))(28.(1<.$<.$<.)))R5.R3.)P,(3>.Vsegs,R6.R4.)P,(3:.Vsegs,R5.)P,(20.Vsegs,R6.(9.VdX,)(21.(22.R7.)(23.&40.R5.)(13.R7.)(24.VdX,)))P,(>.(;.$<.R6.+1.)(;.$<.R6.-1.))P,(39.Vsegs,VR,VHIA,R<.R;.VLF,R8.)P,(31.Vsegs,(32.VR,)(33.Vsegs,VR,VHIA,R=.)R9.(9.VdX,)+10.)(19.(28.$15.)R10.R?.R>.R=.R:.(43.(9.R;.)R9.(13.R;.)(22.R;.)(12.R;.)(24.R;.)(26.R;.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f hc LBc mc dXc m' sg' J MU WM MI' CX' SG' HH' OX'.
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption.
    - eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. cbn. clear - DSX LOSP FS16; lia.
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. cbn. rewrite FSZ. clear - DSX LOSP; lia.
    - pose proof MX1 as [(CX & XAL' & X0' & LEN0 & NR0 & OW) _]. split; [| exact SG']. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [rewrite AD1, PD1; exact CX'|]. split; [exact XAL'|]. split; [exact X0'|]. split; [exact LEN0|]. split; [exact NR0|].
      destruct (md_own dXc) eqn:EO2; [exact OW| | exfalso; first [exact (NS1 eq_refl)| exact (NS1 EO2)]].
      ddestruct OW as (O1 & O2 & O3 & O4). split; [exact O1|]. split; [exact O2|]. split; [exact O3|].
      eapply u32arr_transport; [exact O4| exact MU| exact WM|]. cbn. pose proof (XP1 eq_refl). rewrite AD1 in *. clear - H LEN0 NR0; lia.
    - eapply presA_trans; [exact HPX1|]. rewrite <- HS1.
      eapply (presA_of_munch segs R (mpd_keep LB dX) LF _ _ _ _ mc m' (hcs segs R HIA hc) (hcs_ok segs R HIA hc)); [| | exact MU| exact WM].
      + unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (X + 16 - X) with 16 by (clear; lia). eapply aobj_crange. exact OX1.
      + intros c0 Hc. eapply cshd_hcs; [exact HH1| | eapply cshd_mono_lb; [exact Hc| intros b Hb; exact (xa_keep_sub _ _ _ _ _ _ _ _ J Hb)]]. clear; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_binop : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Pmc,P,(11.&40.)(17.(11.&8.))Pm',P,(11.&40.)(17.(11.&8.))Ph',(16.Vsegs,VR,VHIA,)PLB',(14.$15.)PdX',$18.PSPc,$<.PPHI',$<.PFR',$<.P,(19.(28.$15.)R:.R9.Vh,VLB,R8.VdX,)P,(0.(1.Vlo,R4.)(1.R4.(2.(3.&40.Vsp,)VFS,)))P,(1.=R4.)P,(1.=R4.)P,(3:.Vsegs,R;.)P,(3;.Vsegs,R<.Vlo,(2.(3.&40.Vsp,)VFS,))P,(44.Vsegs,VR,(61.VLB,VdX,)VLF,R9.(8.VR,)(45.Vsegs,VR,VHIA,Vh,)(3=.(1<.$<.$<.)(2<.$<.$<.(9.VdX,)(:.(9.VdX,)+10.))(28.(1<.$<.$<.)))R>.R=.)P,(;.$<.(36.Vsegs,VR,VHIA,R=.)(36.Vsegs,VR,VHIA,Vh,))P,(;.$<.(45.Vsegs,VR,VHIA,R>.)(45.Vsegs,VR,VHIA,Vh,))P,(;.$<.(46.Vsegs,VR,VHIA,R?.)(46.Vsegs,VR,VHIA,Vh,))P,Px,$<.P,(33.Vsegs,VR,VHIA,Vh,R1.)(33.Vsegs,VR,VHIA,R12.R2.)P,(1.(47.Vsegs,VR,VHIA,R11.)(:.(47.Vsegs,VR,VHIA,Vh,)R=.))P,(1.(48.Vsegs,VR,VHIA,R12.)(:.(48.Vsegs,VR,VHIA,Vh,)R=.))P,(39.Vsegs,VR,VHIA,R13.R12.VLF,R14.)P,(62.Vsegs,R15.R13.R12.)P,(63.VLB,VdX,R14.R13.)P,(64.VLB,VdX,R14.)P,Pb,$15.P,(2;.$15.R1.(38.R16.))(>.(2;.$15.R2.(38.VdX,))(49.VR,(61.VLB,VdX,)VLF,(1=.$<.$<.R2.)(65.$<.$<.R2.)))(19.(28.$15.)(:.R1<.R14.)(:.R1;.R13.)R18.R17.R19.R16.)")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f mc m' h' LB' dX' SPc PHI' FR' J HSPc HPHI HFR MI' ST' HP HT' HS' HF' HCS' HV' HFR' HH' MX' OUT' BK FRA'.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    dpose OUT' as (OA & ONS & O3 & O4 & O5). dpose BK as (BA & BP & BF & BN).
    destruct XW as [CW DXP].
    pose proof (client_wrange_keep L LB LF SP (htop segs R HIA h) dX X 16 CW DXP) as CWk.
    assert (CRk : client_range L (mpd_keep LB dX ++ fdata LF) SPc X 16).
    { eapply client_range_inside; [eapply client_wrange_sp_mono; [| exact CWk]; clear - HSPc FS16; lia| intros b Hb; exact Hb| clear; lia| clear; lia]. }
    pose proof MX' as [(CX' & _ & _ & LEN' & NR' & OW') SG']. rewrite OA, BP in CX'.
    constructor; cbn [app]; try assumption.
    - eapply (presA_rw_cells segs R); [exact HP| exact FR1| rewrite FSZ; apply client_range_stack; clear - HSPc; lia| rewrite FSZ; cbn [disjoint_from]; split; [clear - DSX LOSP FS16; lia| exact I]].
    - clear - HV' HV1 HPHI. lia.
    - clear - HFR' HFR1 HFR. lia.
    - eapply presA_trans; [exact HPX1|].
      eapply presA_weaken; [exact HP| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - HSPc LOSP FS16; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
    - eapply aobj_cs_mono; [exact HCS'|].
      eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA h)| exact HP| exact OX1| intros x Hx; eapply hcs_below_top; exact Hx|].
      right. split; [exact CRk| clear - ALO LOS HSPc; lia].
    - (* [comment removed for export] *)
      intros EO. destruct (FRA' (md_p dX', 4 * md_n dX') ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [Hb|HFRA].
      + assert (EOX : md_own dX = LHeap /\ md_p dX = md_p dX' /\ md_n dX = md_n dX').
        { unfold mpd_blk in Hb. destruct (md_own dX); try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as E1 E2.
          split; [reflexivity| split; [exact E1| clear - E2; lia]]. }
        ddestruct EOX as (EOd & EP & EN). destruct (XP1 EOd); [left| right]; rewrite <- ?EP, <- ?EN; assumption.
      + cbn [fst snd] in HFRA. rewrite EO in OW'. destruct OW' as (N1' & _).
        destruct (fresh_apart_client R (mpd_keep LB dX) LF SPc X 16 _ _ HFRA CRk ltac:(clear; lia) ltac:(clear - N1'; lia) ltac:(clear - ALO LOS HSPc; lia)); [right| left]; assumption.
    - (* [comment removed for export] *)
      intros ON. assert (EO : md_own dX' = LHeap) by (destruct (md_own dX'); [exfalso; exact (ON eq_refl)| reflexivity| exfalso; exact (ONS eq_refl)]).
      destruct (FRA' (md_p dX', 4 * md_n dX') ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [Hb|HFRA].
      + assert (EOX : md_own dX = LHeap /\ md_p dX = md_p dX' /\ md_n dX = md_n dX').
        { unfold mpd_blk in Hb. destruct (md_own dX); try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as E1 E2.
          split; [reflexivity| split; [exact E1| clear - E2; lia]]. }
        ddestruct EOX as (EOd & EP & EN). destruct (XLS1 ltac:(rewrite EOd; discriminate)); [left| right]; rewrite <- ?EP, <- ?EN; assumption.
      + cbn [fst snd] in HFRA. dpose HFRA as (_ & AC' & _). left. clear - AC' ALO LOS. lia.
    all: match goal with |- ?g => idtac "XB-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable dB : mpd.
  Record JBA : Prop := {
    jb_MB0 : opnd_atA segs R LF m LB SP dB;
    jb_OB : opnd_sep dX dB lo SP;
    jb_CRB : client_range L (LB ++ fdata LF) lo (md_addr dB) 16;
    jb_CRBL : md_own dB = LHeap -> client_range L (LB ++ fdata LF) lo (md_p dB) (4 * md_n dB);
    jb_SXB : X + 16 <= md_addr dB \/ md_addr dB + 16 <= X;
    (* [comment removed for export] *)
    jb_IMG : md_own dB = LStatic -> (forall i, 0 <= i < 4 * md_n dB -> ro_addr segs (wa (md_p dB + i)) = true) ->
             forall hc LBc mc, HM segs R HIA hc LBc LF mc -> aobj segs AL (hcs segs R HIA hc) mc (md_p dB) (4 * md_n dB) }.
  Hypothesis DBJ : JBA.
  Local Ltac jb_open := pose proof DBJ as [MB0 OB CRB CRBL SXB BIMG].

  Record BJA (hc : HST segs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) : Prop := {
    bj_at : opnd_atA segs R LF mc LBc SP dB;
    bj_sepS : md_own dXc = LHeap -> md_addr dB + 16 <= md_p dXc \/ md_p dXc + 4 * md_n dXc <= md_addr dB;
    bj_sepL : md_own dXc = LHeap -> md_own dB <> LNull -> md_p dXc + 4 * md_n dXc <= md_p dB \/ md_p dB + 4 * md_n dB <= md_p dXc;
    bj_aobj : aobj segs AL (hcs segs R HIA hc) mc (md_addr dB) 16;
    bj_aobjL : md_own dB <> LNull -> aobj segs AL (hcs segs R HIA hc) mc (md_p dB) (4 * md_n dB)
  }.

  #[using="h m dX FS FRAME JC DBJ"] Lemma bja_facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.P,(66.R4.R3.R2.R1.)(0.(4.=(9.VdB,))(0.(1.(:.(9.VdB,)+10.)(5.+2.+40.))(0.(;.$<.(=.(9.VdB,)+8.)=)(0.(;.$<.(?.(10.(11.&40.)(12.VdB,)))(13.VdB,))(0.(0.(1.=(13.VdB,))(1.(13.VdB,)+2710.))(0.(>.(1.(:.(9.VdB,)+10.)Vlo,)(1.(3.&40.Vsp,)(9.VdB,)))(0.P,(;.$25.(26.VdB,)$27.)(0.(;.$<.(22.VdB,)=)(;.$<.(13.VdB,)=))P,(29.(;.$25.(26.VdB,)$27.))(0.(1.+1.(13.VdB,))(0.(4.=(22.VdB,))(0.(;.$<.(=.(22.VdB,)+4.)=)(0.(4?.Vsegs,R4.(22.VdB,)(50.(12.VdB,)))(0.(>.(1.(:.(22.VdB,)(2=.+4.(13.VdB,)))Vlo,)(1.(3.&40.Vsp,)(22.VdB,)))(0.P,(;.$25.(26.VdB,)$2:.)(0.(2;.(1<.$<.$<.)(2<.$<.$<.(22.VdB,)(2=.+4.(13.VdB,)))VLB,)(2;.(1<.$<.$<.)(2<.$<.$<.(22.VdB,)(2=.+4.(13.VdB,)))R6.))P,(;.$25.(26.VdB,)$67.)(>.Pi,$<.P,(0.(1.=R1.)(4.R1.(2=.+4.(13.VdB,))))(;.$68.(69.Vsegs,(6:.(:.(22.VdB,)R2.)))$6;.)(0.(37.(7.VR,)(35.VLF,)(3.&40.Vsp,)(22.VdB,)(2=.+4.(13.VdB,)))(4.(:.(22.VdB,)(2=.+4.(13.VdB,)))(5.+2.+40.)))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open.
    intros hc LBc mc dXc B. pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ B)) as [(CBc & BAL & B0 & LENB & NRB & OWNB) SGB].
    pose proof (rw_cells_bound _ _ _ _ CBc) as BB. unfold mpi_cells in BB. cbn [cells_size csize Nat.add] in BB. unfold MPI_MAX_LIMBS in NRB.
    dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5). destruct (hm_apart segs R HIA h LB LF m HH) as [HF0 _]. rewrite Forall_forall in HF0.
    split; [exact B0|]. split; [clear - BB; lia|]. split; [exact BAL|]. split; [exact LENB|]. split; [exact NRB|]. split; [exact OB4|].
    split; [intros EO; rewrite EO in OWNB; exact OWNB|].
    intros BN. pose proof (opnd_viewA _ _ _ _ _ _ _ MB0) as [(_ & _ & _ & _ & _ & OWNB0) _].
    destruct (md_own dB); [exfalso; exact (BN eq_refl)| |].
    - ddestruct OWNB as (N1 & BIN & BPAL & BARR). ddestruct OWNB0 as (_ & BIN0 & _).
      destruct (HF0 _ ltac:(apply in_or_app; left; exact BIN0)) as (R0 & R1 & _). cbn in R0, R1.
      split; [exact N1|]. split; [exact R0|]. split; [clear - BPAL R0; Z.div_mod_to_equations; lia|]. split; [apply u32arr_ro; exact BARR|]. split; [exact (OB5 BN)|].
      split; [intros _; split; assumption| intros E; discriminate E].
    - ddestruct OWNB as (N1 & BPAL & BP0 & BBY & BRO). split; [exact N1|]. split; [exact BP0|]. split; [exact BPAL|]. split; [exact BBY|]. split; [exact (OB5 BN)|].
      split; [intros E; discriminate E| intros _; exact BRO].
  Qed.

  (* [comment removed for export] *)
  #[using="JC DBJ"] Lemma bja_client : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PLBn,(14.$15.)PSPn,$<.P,(19.R9.R8.R7.R6.R5.R4.R3.)P,(66.R7.R6.R5.R4.)P,Pb,$15.P,(2;.$15.R1.R8.)P,P,(;.$25.(26.R7.)$2:.)(29.(;.$15.R3.(2<.$<.$<.(22.R8.)(2=.+4.(13.R8.)))))(2;.$15.R3.R7.)P,(1.R4.(3.&40.Vsp,))(0.(37.(7.VR,)(1>.$15.R6.(35.VLF,))R5.(9.VdB,)+10.)P,(;.$25.(26.VdB,)$2:.)(37.(7.VR,)(1>.$15.R7.(35.VLF,))R6.(22.VdB,)(2=.+4.(13.VdB,))))")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open.
    intros EX v f hc LBc mc dXc LBn SPn J B SUB LE. dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof (bja_facts _ _ _ _ B) as (B0 & B16 & BAL & LENB & NRB & BS & OWNB0 & OWNB1).
    split.
    - intros a Ha. destruct (CRB a Ha) as [C|[C|([q k] & Hq & Rq)]]; [left; clear - C LE OB4 Ha; lia| right; left; exact C| right; right].
      exists (q, k). split; [| exact Rq]. cbn in Rq. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left| right; exact Hq]. apply SUB.
      + apply (proj1 (proj2 (proj2 (proj2 (xa_out _ _ _ _ _ _ _ J))))); [exact Hq|]. unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail).
        intros [E|[]]. injection E as E1 E2. pose proof (OB2 eq_refl). clear - H E1 E2 Ha Rq. lia.
      + intros EO E. injection E as E1 E2. pose proof (bj_sepS _ _ _ _ B EO). clear - H E1 E2 Ha Rq. lia.
    - intros EO a Ha. ddestruct (OWNB1 ltac:(rewrite EO; discriminate)) as (N1 & P0 & _ & _ & _ & BIN & _). destruct (BIN EO) as [BIN0 BINc].
      right; right. exists (md_p dB, 4 * md_n dB). split; [| cbn; exact Ha]. apply in_app_iff. left. apply SUB; [exact BINc|].
      intros EOX E. injection E as E1 E2. pose proof (bj_sepL _ _ _ _ B EOX ltac:(rewrite EO; discriminate)). clear - H E1 E2 N1. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JC DBJ"] Lemma bja_aobjL_at : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.Ph2,(16.Vsegs,VR,VHIA,)PLB2,(14.$15.)Pm2,P,(11.&40.)(17.(11.&8.))PSPp,$<.PW,(14.$3?.)P,(19.R<.R;.R:.R9.R8.R7.R6.)P,(66.R:.R9.R8.R7.)P,(39.Vsegs,VR,VHIA,R7.R6.VLF,R5.)P,Pb,$15.P,(2;.$15.R1.R<.)(2;.$15.R2.R9.)P,Px,$<.P,(33.Vsegs,VR,VHIA,R>.R1.)(33.Vsegs,VR,VHIA,R;.R2.)P,(44.Vsegs,VR,(1>.$15.R11.R=.)VLF,R7.(8.VR,)(45.Vsegs,VR,VHIA,R>.)R6.R<.R8.)P,(0.(1.Vlo,R8.)(1.R8.(3.&40.Vsp,)))P,(29.(;.$25.(26.VdB,)$27.))(31.Vsegs,(32.VR,)(33.Vsegs,VR,VHIA,R=.)R;.(22.VdB,)(2=.+4.(13.VdB,)))")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros EX v f hc LBc mc dXc h2 LB2 m2 SPp W J B HH2 SUB2 HCS2 HP LE BN.
    pose proof (bja_facts _ _ _ _ B) as (B0 & B16 & BAL & LENB & NRB & BSK & OWNB0 & OWNB1).
    ddestruct (OWNB1 BN) as (N1 & P0 & BPAL & BBY & BSK' & BIN & BRO). pose proof (bj_aobjL _ _ _ _ B BN) as OBL.
    destruct (limb_own_eq_dec (md_own dB) LHeap) as [EO|NEO].
    - destruct (BIN EO) as [_ BINc]. eapply hm_aobj_block; [exact HH2| apply SUB2; exact BINc].
    - destruct (md_own dB) eqn:EOB; [exfalso; exact (BN eq_refl)| exfalso; exact (NEO eq_refl)|].
      destruct (BRO eq_refl) as [RO|[BSP BND]].
      + eapply BIMG; [reflexivity| exact RO| exact HH2].
      + eapply aobj_cs_mono; [exact HCS2|].
        eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hc)| exact HP| exact OBL| intros x Hx; eapply hcs_below_top; exact Hx|].
        right. split; [eapply client_range_temp; [exact BSP| clear - LE; lia| intros b Hb; apply in_or_app; right; exact Hb]| clear - ALO LOS LE; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="JC DBJ"] Lemma bja_transport : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.Pm2,P,(11.&40.)(17.(11.&8.))Ph2,(16.Vsegs,VR,VHIA,)PLB2,(14.$15.)P,(19.R:.R9.R8.R7.R6.R5.R4.)P,(66.R8.R7.R6.R5.)P,(44.Vsegs,VR,(1>.$15.R<.R8.)VLF,(2.(3.&40.Vsp,)VFS,)(8.VR,)(45.Vsegs,VR,VHIA,R9.)(28.$3?.)R7.R5.)P,(3:.Vsegs,R6.)P,Px,$<.P,(33.Vsegs,VR,VHIA,R<.R1.)(33.Vsegs,VR,VHIA,R8.R2.)P,(39.Vsegs,VR,VHIA,R7.R6.VLF,R8.)P,Pb,$15.P,(2;.$15.R1.R=.)(2;.$15.R2.R9.)(66.R9.R=.R:.R;.)")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros EX v f hc LBc mc dXc m2 h2 LB2 J B HP MI2 HCS2 HH2 SUB2. pose proof B as [BA BS BL BO BOL].
    destruct (bja_client EX v f hc LBc mc dXc (EX ++ LBc) (SP - FS) J B ltac:(intros b Hb _; apply in_or_app; right; exact Hb) ltac:(clear - FS16; lia)) as [C1 C2].
    constructor; [| exact BS| exact BL| |].
    - eapply opnd_atA_heap_presx; [exact BA| exact (presA_presx segs R _ _ _ _ _ _ _ _ HP)| exact (xa_mi _ _ _ _ _ _ _ J)| exact MI2| exact C1| exact C2| cbn; exact I| intros _; cbn; exact I| | clear - FS16; lia
                                  | intros b Hb; apply in_or_app; right; exact Hb].
      intros b Hb. unfold mpd_blk in Hb. pose proof (opnd_viewA _ _ _ _ _ _ _ BA) as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dB); try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)).
    - eapply aobj_cs_mono; [exact HCS2|].
      eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hc)| exact HP| exact BO| intros x Hx; eapply hcs_below_top; exact Hx|].
      right. split; [exact C1| clear - ALO LOS LOSP; lia].
    - eapply (bja_aobjL_at EX v f hc LBc mc dXc h2 LB2 m2 (SP - FS) []); try eassumption. clear - LOSP FS16; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma bja_munch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "PEX,(14.$15.)Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PW,(14.$3?.)Pm',P,(11.&40.)(17.(11.&8.))P,(19.R9.R8.R7.R6.R5.R4.R3.)P,(66.R7.R6.R5.R4.)P,(3<.R4.R6.R3.)P,(3>.Vsegs,R7.R4.)P,(6<.(33.Vsegs,VR,VHIA,R:.)R6.)P,(41.R7.(9.VdB,)+10.)P,P,(29.(;.$25.(26.VdB,)$27.))(41.R9.(22.VdB,)(2=.+4.(13.VdB,)))(66.R=.R<.R8.R:.)")
(* [comment removed for export] *).
  Proof.
    intros EX v f hc LBc mc dXc W m' J [BA BS BL BO BOL] MU WM WC D1 D2. constructor; [| exact BS| exact BL| |].
    - eapply opnd_atA_munch_any; eassumption.
    - eapply (aobj_munch segs AL _ (hcs_ok segs R HIA hc) W mc m'); [exact WC| exact MU| exact BO].
    - intros BN. eapply (aobj_munch segs AL _ (hcs_ok segs R HIA hc) W mc m'); [exact WC| exact MU| exact (BOL BN)].
  Qed.

  #[using="JC DBJ"] Lemma bja_zfree : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))Pm4,P,(11.&40.)(17.(11.&8.))Ph4,(16.Vsegs,VR,VHIA,)P,(19.(3=.(1<.$<.$<.)(2<.$<.$<.R5.(2=.+4.R4.))(28.(1<.$<.$<.)))R;.R:.R9.R8.R7.R6.)P,(4>.R9.R6.R5.R4.R8.R7.)P,(66.R;.R:.R9.R8.)P,(;.$25.(26.R9.)$2:.)P,(44.Vsegs,VR,(55.(22.R:.)(3=.(1<.$<.$<.)(2<.$<.$<.R9.(2=.+4.R8.))R<.))VLF,(2.(3.&40.Vsp,)VFS,)(8.VR,)(45.Vsegs,VR,VHIA,R=.)(3=.(1<.$<.$<.)(2<.$<.$<.(22.R:.)(:.(22.R:.)(2=.+4.(13.R:.))))(28.(1<.$<.$<.)))R;.R6.)P,(3:.Vsegs,R7.)P,Px,$<.P,(33.Vsegs,VR,VHIA,R10.R1.)(33.Vsegs,VR,VHIA,R9.R2.)P,(39.Vsegs,VR,VHIA,R8.(55.(22.R=.)(3=.(1<.$<.$<.)(2<.$<.$<.R<.(2=.+4.R;.))R?.))VLF,R9.)(66.R9.(55.(22.R>.)R10.)R:.R>.)")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f hc LBc mc dXc An cnt ys m4 h4 J F B EO HP4 MI4 HCS4 HH4. pose proof B as [BA BS BL BO BOL].
    pose proof (xa_facts _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
    pose proof F as [FRn FR0 A16 NEW NEWC APA ARR LENY CNT FXS ALO']. dpose FRn as (An0 & AnC & AnD & HAP).
    assert (NEA : An <> md_p dXc) by (destruct (APA _ _ ltac:(apply in_or_app; left; exact XIN)); clear - H CNT N1; lia).
    pose proof (lb_remove_cons_other An (4 * cnt) (md_p dXc) LBc NEA) as ELB. rewrite ELB in HH4. rewrite ELB in HP4.
    assert (NDc : List.NoDup (map fst LBc)) by (cbn in ND1; inversion ND1; assumption).
    assert (SUB : forall b, In b LBc -> (md_own dXc = LHeap -> b <> (md_p dXc, 4 * md_n dXc)) -> In b ((An, 4 * cnt) :: lb_remove (md_p dXc) LBc)).
    { intros [q k] Hb NE. right. eapply in_lb_remove_other; [exact NDc| exact XIN| exact Hb| exact (NE EO)]. }
    destruct (bja_client _ v f hc LBc mc dXc _ (SP - FS) J B SUB ltac:(clear - FS16; lia)) as [C1 C2].
    pose proof (bja_facts _ _ _ _ B) as (B0 & B16 & BAL & LENB & NRB & BSK & OWNB0 & OWNB1).
    (* [comment removed for export] *)
    constructor; [| exact BS| exact BL| |].
    - eapply opnd_atA_heap_presx; [exact BA| exact (presA_presx segs R _ _ _ _ _ _ _ _ HP4)| exact (xa_mi _ _ _ _ _ _ _ J)| exact MI4| exact C1| exact C2
                                 | cbn; pose proof (BS EO); clear - H; lia| intros BN; cbn; pose proof (BL EO BN); clear - H; lia| | clear - FS16; lia
                                 | intros b Hb; apply in_or_app; right; exact Hb].
      intros b Hb. unfold mpd_blk in Hb. destruct (md_own dB) eqn:EOB; try (destruct Hb; fail). destruct Hb as [<-|[]].
      ddestruct (OWNB1 ltac:(discriminate)) as (_ & _ & _ & _ & _ & BIN & _). destruct (BIN eq_refl) as [_ BINc].
      eapply in_lb_remove_other; [exact NDc| exact XIN| exact BINc|]. intros E. injection E as E1 E2. pose proof (BL EO ltac:(discriminate)). clear - H E1 E2 N1. lia.
    - eapply aobj_cs_mono; [exact HCS4|].
      eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hc)| exact HP4| exact BO| intros x Hx; eapply hcs_below_top; exact Hx|].
      right. split; [exact C1| clear - ALO LOS LOSP; lia].
    - intros BN. ddestruct (OWNB1 BN) as (N1' & P0' & BPAL & BBY & BSK' & BIN & BRO).
      destruct (limb_own_eq_dec (md_own dB) LHeap) as [EOB|NEO].
      + destruct (BIN EOB) as [_ BINc]. eapply hm_aobj_block; [exact HH4|]. right.
        eapply in_lb_remove_other; [exact NDc| exact XIN| exact BINc|]. intros E. injection E as E1 E2. pose proof (BL EO BN). clear - H E1 E2 N1. lia.
      + destruct (md_own dB) eqn:EOB; [exfalso; exact (BN eq_refl)| exfalso; exact (NEO eq_refl)|].
        destruct (BRO eq_refl) as [RO|[BSP BND]].
        * eapply BIMG; [reflexivity| exact RO| exact HH4].
        * eapply aobj_cs_mono; [exact HCS4|].
          eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hc)| exact HP4| exact (BOL BN)| intros x Hx; eapply hcs_below_top; exact Hx|].
          right. split; [eapply client_range_temp; [exact BSP| clear - FS16; lia| intros b Hb; apply in_or_app; right; exact Hb]| clear - ALO LOS LOSP; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="JC DBJ"] Lemma bja_fb_apart : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phc,(16.Vsegs,VR,VHIA,)PLBc,(14.$15.)Pmc,P,(11.&40.)(17.(11.&8.))PdXc,$18.PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))P,(19.(3=.(1<.$<.$<.)(2<.$<.$<.R3.(2=.+4.R2.))(28.(1<.$<.$<.)))R9.R8.R7.R6.R5.R4.)P,(4>.R7.R4.R3.R2.R6.R5.)P,(66.R9.R8.R7.R6.)(0.(>.(1.(:.(9.VdB,)+10.)R6.)(1.(:.R6.(2=.+4.R5.))(9.VdB,)))P,(29.(;.$25.(26.VdB,)$27.))(>.(1.(:.R7.(2=.+4.R6.))(22.VdB,))(1.(:.(22.VdB,)(2=.+4.(13.VdB,)))R7.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f hc LBc mc dXc An cnt ys J F B. pose proof B as [BA BS BL BO BOL].
    pose proof F as [FRn FR0 A16 NEW NEWC APA ARR LENY CNT FXS ALO']. dpose FRn as (An0 & AnC & AnD & HAP). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof (bja_facts _ _ _ _ B) as (B0 & B16 & BAL & LENB & NRB & BSK & OWNB0 & OWNB1).
    destruct (bja_client _ v f hc LBc mc dXc LBc lo J B ltac:(intros b Hb _; exact Hb) ltac:(clear - LOSP FS16; lia)) as [C1 C2].
    split.
    - destruct (client_range_apart L (LBc ++ fdata LF) lo (md_addr dB) 16 An (4 * cnt) C1) as [D|D]; try assumption; first [clear - D; lia| clear - CNT NRB ALO LOS AnC; lia].
    - intros BN. ddestruct (OWNB1 BN) as (N1 & P0 & BPAL & BBY & BSK' & BIN & BRO).
      destruct (limb_own_eq_dec (md_own dB) LHeap) as [EOB|NEO].
      + destruct (BIN EOB) as [_ BINc]. exact (APA _ _ ltac:(apply in_or_app; left; exact BINc)).
      + destruct (md_own dB) eqn:EOB; [exfalso; exact (BN eq_refl)| exfalso; exact (NEO eq_refl)|].
        destruct (BRO eq_refl) as [RO|[BSP BND]];
          [| exact (fresh_apart_client R LBc LF lo (md_p dB) (4 * md_n dB) An (4 * cnt) FRn
                      ltac:(eapply client_range_temp; [exact BSP| clear - LOSP FS16; lia| intros b Hb; apply in_or_app; right; exact Hb])
                      ltac:(clear - N1; lia) ltac:(clear - CNT NRB; lia) ltac:(clear - ALO LOS; lia))].
        pose proof (u32ro_bound _ _ _ _ BBY) as BB.
        pose proof (ROIMG (md_p dB + 0) (RO 0 ltac:(clear - N1; lia)) ltac:(clear - BB P0 N1 LENB; lia)) as I0.
        pose proof (ROIMG (md_p dB + (4 * md_n dB - 1)) (RO (4 * md_n dB - 1) ltac:(clear - N1; lia)) ltac:(clear - BB P0 N1 LENB; lia)) as I1.
        destruct (hm_apart segs R HIA hc ([(An, 4 * cnt)] ++ LBc) LF mc (xa_hm _ _ _ _ _ _ _ J)) as [HFc _]. rewrite Forall_forall in HFc.
        ddestruct (HFc (An, 4 * cnt) ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & _ & AI). cbn in AI.
        clear - I0 I1 AI N1 CNT NR. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JC DBJ"] Lemma bja_finish : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Phd,(16.Vsegs,VR,VHIA,)PLBd,(14.$15.)PAn,$<.Pcnt,$<.Pys,(14.(11.&40.))Pme,P,(11.&40.)(17.(11.&8.))PdXc,$18.Pm5,P,(11.&40.)(17.(11.&8.))P,(54.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(66.R9.R8.R4.R3.)P,(3<.(3=.(1<.$<.$<.)(2<.$<.$<.(9.VdX,)(:.(9.VdX,)+10.))(28.(1<.$<.$<.)))R5.R3.)P,(3>.Vsegs,R6.R4.)(66.R<.(3=.(1<.$<.$<.)(2<.$<.$<.R:.(2=.+4.R9.))R;.)R5.(43.(9.VdX,)(1?.R6.)R9.R:.R8.(24.VdX,)$2:.))")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f hd LBd An cnt ys me dXc m5 D B MU WM. pose proof B as [BA BS BL BO BOL].
    pose proof D as [MI4 ST4 FR4 HH4 HT4 HS4 HF4 HCS4 HV4 HFR4 CX4 SG SUB KEEP GONE NEW APA ARR LENY CNT DXS HPX4 FR0 A16 OX4 ALO' NMX].
    dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof (bja_facts _ _ _ _ B) as (B0 & B16 & BAL & LENB & NRB & BSK & OWNB0 & OWNB1).
    (* [comment removed for export] *)
    assert (CRB' : client_range L (LBd ++ fdata LF) lo (md_addr dB) 16).
    { intros a Ha. destruct (CRB a Ha) as [C|[C|([q k] & Hq & Rq)]]; [left; exact C| right; left; exact C| right; right].
      exists (q, k). split; [| exact Rq]. cbn in Rq. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left| right; exact Hq].
      apply KEEP; [exact Hq|]. unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail).
      intros [E|[]]. injection E as E1 E2. pose proof (OB2 eq_refl). clear - H E1 E2 Ha Rq. lia. }
    assert (BSA : md_addr dB + 16 <= An \/ An + 4 * cnt <= md_addr dB).
    { dpose FR0 as (A0' & AC & AD & _).
      destruct (client_range_apart L (LBd ++ fdata LF) lo (md_addr dB) 16 An (4 * cnt) CRB') as [D0|D0]; try assumption; first [clear - D0; lia| clear - CNT ALO LOS AC AD; lia]. }
    assert (BLA : md_own dB <> LNull -> An + 4 * cnt <= md_p dB \/ md_p dB + 4 * md_n dB <= An).
    { intros BN. ddestruct (OWNB1 BN) as (N1 & P0 & BPAL & BBY & BSK' & BIN & BRO).
      destruct (limb_own_eq_dec (md_own dB) LHeap) as [EOB|NEO].
      - destruct (BIN EOB) as [_ BINd]. exact (APA _ _ ltac:(apply in_or_app; left; exact BINd)).
      - destruct (md_own dB) eqn:EOB; [exfalso; exact (BN eq_refl)| exfalso; exact (NEO eq_refl)|].
        destruct (BRO eq_refl) as [RO|[BSP BND]].
        2:{ dpose FR0 as (A0' & AC & AD & _).
            destruct (client_range_apart L (LBd ++ fdata LF) lo (md_p dB) (4 * md_n dB) An (4 * cnt)
                        ltac:(eapply client_range_temp; [exact BSP| clear - LOSP FS16; lia| intros b Hb; apply in_or_app; right; exact Hb])) as [D0|D0];
              try assumption; first [left; exact D0| right; exact D0| clear - CNT N1 ALO LOS AC AD; lia]. }
        pose proof (u32ro_bound _ _ _ _ BBY) as BB.
        pose proof (ROIMG (md_p dB + 0) (RO 0 ltac:(clear - N1; lia)) ltac:(clear - BB P0 N1 LENB; lia)) as I0.
        pose proof (ROIMG (md_p dB + (4 * md_n dB - 1)) (RO (4 * md_n dB - 1) ltac:(clear - N1; lia)) ltac:(clear - BB P0 N1 LENB; lia)) as I1.
        destruct (hm_apart segs R HIA hd ((An, 4 * cnt) :: LBd) LF me HH4) as [HFc _]. rewrite Forall_forall in HFc.
        ddestruct (HFc (An, 4 * cnt) ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & _ & AI). cbn in AI.
        clear - I0 I1 AI N1 CNT NR. lia. }
    assert (WC : w_client (hcs segs R HIA hd) [(X, X + 16)]).
    { unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (X + 16 - X) with 16 by (clear; lia). eapply aobj_crange. exact OX4. }
    constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
    - eapply opnd_atA_munch_any; [| exact MU| exact WM| cbn; clear - SXB; lia| intros BN; cbn; pose proof (OB1 BN); clear - H; lia].
      eapply opnd_atA_blocks; [exact BA|]. intros b Hb. right. unfold mpd_blk in Hb.
      pose proof (opnd_viewA _ _ _ _ _ _ _ BA) as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dB); try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)).
    - intros _. exact BSA.
    - intros _ BN. destruct (BLA BN); [left| right]; assumption.
    - eapply (aobj_munch segs AL _ (hcs_ok segs R HIA hd) _ me m5); [exact WC| exact MU| exact BO].
    - intros BN. eapply (aobj_munch segs AL _ (hcs_ok segs R HIA hd) _ me m5); [exact WC| exact MU| exact (BOL BN)].
  Qed.
  (* [comment removed for export] *)
  #[using="JC DBJ"] Lemma bja_binop : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey ()) "Pv,$<.Pf,$<.Pmc,P,(11.&40.)(17.(11.&8.))Pm',P,(11.&40.)(17.(11.&8.))Ph',(16.Vsegs,VR,VHIA,)PLB',(14.$15.)PdX',$18.PSPc,$<.P,(19.(28.$15.)R8.R7.Vh,VLB,R6.VdX,)P,(66.Vh,VLB,R7.VdX,)P,(0.(1.Vlo,R3.)(1.R3.(2.(3.&40.Vsp,)VFS,)))P,(3:.Vsegs,R8.)P,(44.Vsegs,VR,(61.VLB,VdX,)VLF,R5.(8.VR,)(45.Vsegs,VR,VHIA,Vh,)(3=.(1<.$<.$<.)(2<.$<.$<.(9.VdX,)(:.(9.VdX,)+10.))(28.(1<.$<.$<.)))R:.R9.)P,Px,$<.P,(33.Vsegs,VR,VHIA,Vh,R1.)(33.Vsegs,VR,VHIA,R;.R2.)P,(39.Vsegs,VR,VHIA,R:.R9.VLF,R;.)P,(62.Vsegs,R<.R:.R9.)P,(63.VLB,VdX,R;.R:.)P,Pb,$15.P,(2;.$15.R1.(38.R<.))(>.(2;.$15.R2.(38.VdX,))(49.VR,(61.VLB,VdX,)VLF,(1=.$<.$<.R2.)(65.$<.$<.R2.)))(66.R>.R=.R?.R<.)")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open. dpose jca_facts as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f mc m' h' LB' dX' SPc J B HSPc MI' HP HCS' HH' MX' OUT' FRA'.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    pose proof B as [BA BS BL BO BOL]. dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5). dpose OUT' as (OA & ONS & O3 & O4 & O5).
    pose proof (bja_facts _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof MX' as [(_ & _ & _ & LEN' & NR' & OW') SG'].
    assert (CRBk : client_range L (mpd_keep LB dX ++ fdata LF) SPc (md_addr dB) 16).
    { eapply client_range_sep; [eapply client_range_keep; [exact CRB| exact OB2]| intros b Hb; exact Hb| clear - OB4 HSPc FS16; lia]. }
    constructor.
    - (* [comment removed for export] *)
      eapply (opnd_atA_heap_presx segs R LF mc m' LB (mpd_keep LB dX ++ fdata LF) LB' SPc SP [(X, X + 16)]);
        [exact BA| exact (presA_presx segs R _ _ _ _ _ _ _ _ HP)| exact MI1| exact MI'| exact CRBk| | cbn; split; [clear - SXB; lia| exact I]
        | intros BN; cbn; split; [pose proof (OB1 BN); clear - H; lia| exact I]| | clear - HSPc FS16; lia| intros b Hb; apply in_or_app; right; exact Hb].
      + intros EO. eapply client_range_sep; [eapply client_range_keep; [exact (CRBL EO)|]| intros b Hb; exact Hb| destruct (OB5 ltac:(rewrite EO; discriminate)); clear - H HSPc FS16; lia].
        intros EOX. destruct OB3 as [C|[C|[C|C]]]; [exfalso; rewrite C in SXB; clear - SXB; lia| exfalso; exact (C EOX)| exfalso; rewrite C in EO; discriminate| clear - C; lia].
      + intros b Hb. unfold mpd_blk in Hb. destruct (md_own dB) eqn:EOB; try (destruct Hb; fail). destruct Hb as [<-|[]].
        ddestruct (OWNE1 ltac:(congruence)) as (NB1 & _ & _ & _ & _ & BHP & _). destruct (BHP eq_refl) as [BIN _].
        apply O4; [exact BIN|].
        unfold mpd_blk. destruct (md_own dX) eqn:EOX; try (intros []; fail). intros [E|[]]. injection E as Q1 Q2.
        destruct OB3 as [C|[C|[C|C]]]; [rewrite C in SXB; clear - SXB; lia| exact (C eq_refl)| discriminate|].
        pose proof MX1 as [(_ & _ & _ & _ & _ & OWX) _]. rewrite EOX in OWX. pose proof (proj1 OWX) as NX1. clear - C Q1 Q2 NB1 NX1. lia.
    - (* [comment removed for export] *)
      intros EO. rewrite EO in OW'. destruct OW' as (N1' & _).
      destruct (new_limbs_apartA R LB LF SPc dX dX' (md_addr dB) 16 FRA' EO N1' ltac:(eapply client_range_sep; [exact CRB| intros b Hb; exact Hb| clear - OB4 HSPc FS16; lia]) OB2 ltac:(clear - ALO LOS HSPc; lia) ltac:(clear; lia)); [left| right]; assumption.
    - (* [comment removed for export] *)
      intros EO BN. rewrite EO in OW'. destruct OW' as (N1' & _). ddestruct (OWNE1 BN) as (NB1 & BP0 & _ & BBY & BSK & BHP & BST).
      destruct (md_own dB) eqn:EOB; [exfalso; exact (BN eq_refl)| |].
      + destruct (new_limbs_apartA R LB LF SPc dX dX' (md_p dB) (4 * md_n dB) FRA' EO N1'
                   ltac:(eapply client_range_sep; [exact (CRBL eq_refl)| intros b Hb; exact Hb| clear - BSK HSPc FS16; lia])
                   ltac:(intros EOX; destruct OB3 as [C|[C|[C|C]]]; [exfalso; rewrite C in SXB; clear - SXB; lia| exfalso; exact (C EOX)| discriminate| clear - C; lia])
                   ltac:(clear - ALO LOS HSPc; lia) ltac:(clear - NB1; lia)); [right| left]; assumption.
      + (* [comment removed for export] *)
        destruct (FRA' (md_p dX', 4 * md_n dX') ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [Hb|HFRA].
        * assert (EOX : md_own dX = LHeap /\ md_p dX = md_p dX' /\ md_n dX = md_n dX').
          { unfold mpd_blk in Hb. destruct (md_own dX); try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as E1 E2.
            split; [reflexivity| split; [exact E1| clear - E2; lia]]. }
          ddestruct EOX as (EOd & EP & EN). rewrite <- EP, <- EN. apply (BL EOd). congruence.
        * cbn [fst snd] in HFRA. dpose HFRA as (A0' & AC' & AD' & _).
          destruct (BST eq_refl) as [BRO|[BSP BH]].
          -- pose proof MX' as [(_ & _ & _ & _ & _ & OWn) _]. rewrite EO in OWn. ddestruct OWn as (_ & PIN & _).
             destruct (hm_apart segs R HIA h' LB' LF m' HH') as [HF' _]. rewrite Forall_forall in HF'.
             destruct (HF' _ ltac:(apply in_app_iff; left; exact PIN)) as (_ & _ & _ & BI). cbn [fst snd] in BI.
             pose proof (ROIMG (md_p dB + 0) (BRO 0 ltac:(clear - NB1; lia)) ltac:(pose proof (u32ro_bound _ _ _ _ BBY) as BB; clear - BB NB1 LENE; lia)) as I0.
             pose proof (ROIMG (md_p dB + (4 * md_n dB - 1)) (BRO (4 * md_n dB - 1) ltac:(clear - NB1; lia)) ltac:(pose proof (u32ro_bound _ _ _ _ BBY) as BB; clear - BB NB1 LENE; lia)) as I1.
             clear - I0 I1 BI NB1. lia.
          -- exact (fresh_apart_client R (mpd_keep LB dX) LF lo (md_p dB) (4 * md_n dB) (md_p dX') (4 * md_n dX') HFRA
                      ltac:(eapply client_range_temp; [exact BSP| clear - LOSP FS16; lia| intros b Hb; apply in_or_app; right; exact Hb])
                      ltac:(clear - NB1; lia) ltac:(clear - N1'; lia) ltac:(clear - ALO LOS; lia)).
    - (* [comment removed for export] *)
      eapply aobj_cs_mono; [exact HCS'|].
      eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA h)| exact HP| exact BO| intros x Hx; eapply hcs_below_top; exact Hx|].
      right. split; [exact CRBk| clear - ALO LOS HSPc; lia].
    - (* [comment removed for export] *)
      intros BN. ddestruct (OWNE1 BN) as (NB1 & BP0 & _ & BBY & BSK & BHP & BST).
      destruct (md_own dB) eqn:EOB; [exfalso; exact (BN eq_refl)| |].
      + eapply hm_aobj_block; [exact HH'|]. apply O4; [exact (proj1 (BHP eq_refl))|].
        unfold mpd_blk. destruct (md_own dX) eqn:EOX; try (intros []; fail). intros [E|[]]. injection E as Q1 Q2.
        destruct OB3 as [C|[C|[C|C]]]; [rewrite C in SXB; clear - SXB; lia| exact (C eq_refl)| discriminate|].
        pose proof MX1 as [(_ & _ & _ & _ & _ & OWX) _]. rewrite EOX in OWX. pose proof (proj1 OWX) as NX1. clear - C Q1 Q2 NB1 NX1. lia.
      + destruct (BST eq_refl) as [BRO|[BSP BH]].
        * eapply BIMG; [reflexivity| exact BRO| exact HH'].
        * eapply aobj_cs_mono; [exact HCS'|].
          eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA h)| exact HP| exact (BOL BN)| intros x Hx; eapply hcs_below_top; exact Hx|].
          right. split; [eapply client_range_temp; [exact BSP| clear - HSPc FS16; lia| intros b Hb; apply in_or_app; right; exact Hb]| clear - ALO LOS HSPc; lia].
    all: match goal with |- ?g => idtac "BB-LEFT:" g end.
  Qed.

End JA.
