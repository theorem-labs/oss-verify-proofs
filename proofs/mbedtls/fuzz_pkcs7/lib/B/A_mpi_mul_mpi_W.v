(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_copy P_mpi_mul_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_journey2
     A_mpi_zeroize_and_free A_mpi_copy A_mpi_core_mul A_mpi_add_abs_W.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_mpi_mul_mpi_W () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.JCA"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "mm_fr"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "mul_mid_PHI"; "mul_mid_FR"; "mul_mid_SZ"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey2.rideA"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XDA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section REFRAME.
  Variable segs : list Segment.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA segs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Variables (h : HST segs R HIA) (LB LF : list blk) (m : mem) (dX : mpd) (sp : word) (lo FS : Z) (FRAME FRAME' : list cell).
  Local Notation SP := (bv_unsigned sp).
  Local Notation X := (md_addr dX).
  Hypothesis JC : JCA segs R HIA h LB LF m dX sp lo FS FRAME.
  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0>L14331839616.1L19945316590.2L26892418956.1L34955349972.6L35655538626.8L37171002439.5L43674970535.7L43674970535.9L48132467214.8L50797022707.7L51900536031.4L59309011978.4L59309011978.5L62018535662.1L64640219618.1L66566524643.7L67300522439.900000500<00@00L00j01501A01T02202L02[02h03703:03>03J03]S3dXcS2sp2loS2spS1W1a1b1x2HxS4segs1R3HIA1h2sp2lo3TOP5HTOP0S2dX3dXc2E2S2sp2lo1a2HaS2dX2sp2lo3dXc1a2HaS1R2sp2lo2FS3LOS4FS164LOSP3ALOS1R2sp2lo2FS3LOS4FS164LOSPS4segs1R3HIA2hcS3dXc1a2H12RgS2sp2lo1a2H22RgS1RS2dXS2sp2lo1x2RgS2dX2sp2lo3dXc1a2Ha". (* [comment removed for export] *)
  #[using="JC"] Lemma xa_limbs_fr : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "PEX,(0.$1.)Pv,$2.Pf,$2.Phc,(3.Vsegs,VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.PW,(0.$7.)Pm',P,(4.&40.)(5.(4.&8.))Pxs',(0.(4.&40.))P,(8.Vsegs,VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,R:.R9.R8.R7.R6.R5.R4.)P,(9.R4.R6.R3.)P,(:.Vsegs,R7.R4.)P,(;.Vsegs,R5.)P,(<.Vsegs,R6.Vlo,(=.(>.&40.Vsp,)VFS,))P,(?.Vsegs,VR,VHIA,R<.(10.$1.R?.R;.)VLF,R7.)P,Pa,$2.P,(11.(12.R:.R1.))(13.(14.(15.$16.(17.R<.)$18.)(14.(19.(1:.R<.)R2.)(1;.R2.(1<.(1:.R<.)(1=.+4.(1>.R<.))))))(14.(19.Vlo,R2.)(1;.R2.(>.&40.Vsp,))))P,(1?.Vsegs,R9.(=.(>.&40.Vsp,)VFS,)VFRAME',)P,(20.R;.(21.VdX,)+10.)P,(22.Vsegs,R;.(1:.R=.)R:.)P,(15.$23.(24.(4.&40.)R;.)(24.(4.&40.)(25.R>.)))(8.Vsegs,VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME',R15.R14.R13.R12.R11.R=.(26.(21.R?.)(27.R?.)(1>.R?.)(1:.R?.)R<.(28.R?.)(17.R?.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose (jca_facts segs R HIA h LB LF m dX sp lo FS FRAME JC) as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros EX v f hc LBc mc dXc W m' xs' J MU WM MI' ST' HH' HW FR' DS ARR' LEN'.
    pose proof (xa_facts segs R HIA h LB LF m dX sp lo FS FRAME JC _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1 & CX1 & OWN0 & OWN1).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    pose proof (hcs_ok segs R HIA hc) as CSOKc. pose proof (hm_top segs R HIA h LB LF m HH) as HTOP0.
    assert (SCSc : crange (hcs segs R HIA hc) lo (SP - lo)).
    { eapply crange_sub; [exact (hcs_stack segs R HIA hc)| exact LOS| rewrite HS1; clear - HTOP0 TOP; lia]. }
    assert (OUTW : forall a, (md_own dXc <> LHeap \/ md_p dXc + 4 * md_n dXc <= a \/ a < md_p dXc) -> (a < lo \/ SP <= a) -> outside W a).
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
            [| intros b Hb; apply in_or_app; right; exact (xa_keep_sub segs R HIA h LB LF m dX sp lo FS FRAME _ _ _ _ _ _ _ _ J Hb)| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia
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
        eapply (presA_tail0 segs R HIA hc (EX ++ LBc)); [exact HH1| intros b Hb; apply in_or_app; right; exact (xa_keep_sub segs R HIA h LB LF m dX sp lo FS FRAME _ _ _ _ _ _ _ _ J Hb)| exact LOS| rewrite HT1; exact TOP| | exact WM].
        eapply munch_weaken; [| exact MU]. intros a Ha. cbn [outside fst snd] in Ha. apply OUTW; [left; exact NEO| clear - Ha LOSP FS16; lia]. }
    constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End REFRAME.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L37275290198.20L56765667309.2000000C00US2SP3TOP1F3HSP1a2HaS3TOP1F2HF2HT1a2Ha". (* [comment removed for export] *)
Lemma uwc_presA_w : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "PR,$29.PLB,(0.$1.)PLF,(0.$1.)PSP,$2.PSSP,$2.PTOP,$2.PW,(0.$7.)Pm,P,(4.&40.)(5.(4.&8.))Pm',P,(4.&40.)(5.(4.&8.))Pv,$2.PF,$2.Pd,$2.P,(2:.$2;.R<.R;.R:.R9.R8.R7.R6.R5.R4.)P,(2<.$2;.R6.(2=.R=.)R8.R4.R3.R2.)P,(19.R;.R4.)P,Pa,$2.P,(14.(19.R6.R1.)(1;.R1.R;.))(12.R;.R2.)P,(19.=R6.)P,(19.R<.(2>.+2.+40.))(2<.$2;.R:.(2=.R12.)R=.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros R LB LF SP SSP TOP W m m' v F d [P _] UW HSP HW HF HT.
  eapply uwc_transport; [exact UW|]. intros a Ha. apply (proj1 (P a ltac:(lia) ltac:(left; lia) (HW a Ha))).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L58421668439.26L6757932555.25 00000A00BS2LB3LBc3dXc1C2C1S". (* [comment removed for export] *)
Lemma xa_cnt24 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Psegs,(0.$2?.)PR,$29.PHIA,(30.R2.R1.)Ph,(3.R3.R2.R1.)PLB,(0.$1.)PLF,(0.$1.)Pm,P,(4.&40.)(5.(4.&8.))PdX,$6.Psp,(4.&40.)Plo,$2.PFS,$2.PFRAME,(0.$31.)P,(32.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)PEX,(0.$1.)Pv,$2.Pf,$2.Phc,(3.R10.R?.R>.)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.P,(8.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R7.R6.R5.R4.R3.R2.R1.)(19.(33.R4.)(1<.(33.R11.)+1.))")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF m dX sp lo FS FRAME JC EX v f hc LBc mc dXc J.
  pose proof (jca_HND _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)) as ND.
  rewrite map_app in ND. apply NoDup_app_remove_l in ND. apply NoDup_map_inv in ND.
  pose proof (xa_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as (_ & _ & O3 & _).
  assert (INC : incl LBc (LB ++ mpd_blk dXc)). { intros b Hb. apply in_or_app. apply O3. exact Hb. }
  pose proof (cnt24_incl _ _ ND INC) as C. rewrite cnt24_app in C.
  assert (C1 : cnt24 (mpd_blk dXc) <= 1).
  { unfold mpd_blk. destruct (md_own dXc); try (rewrite cnt24_nil; lia).
    pose proof (cnt24_cons_le (md_p dXc, 4 * md_n dXc) []) as C2. rewrite cnt24_nil in C2. exact (proj2 C2). }
  lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


Definition A_WRAP_CALLOC_MM : Z := 0x69484.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMCPY_MM : Z := 0x67dbc.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMSET_MM : Z := 0x68258.    (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mul_mid_PHI (dA dB : mpd) : Z := grow_PHI (md_n dA + md_n dB + 1).
Definition mul_mid_FR (d1 : Z) : Z := calls_FR 2 d1.

(* [comment removed for export] *)
Definition mul_mid_SZ (nX : Z) (dA dB : mpd) : Z := Z.max nX (Z.max (md_n dA + md_n dB) 1).

(* [comment removed for export] *)
Definition mm_fr (c0 c8 c16 c24 c32 c40 c48 c56 : word) : list cell := [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56].

