(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_copy P_mpi_mul_stmt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_journey2
     A_mpi_zeroize_and_free A_mpi_copy A_mpi_core_mul A_mpi_add_abs_W.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_mul_mpi_W () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HST"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.A.A_mpi_journey.XJA"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.LibA.ARt.HM"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Lib.Frame.outside"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.presA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.A.A_mpi_journey.JCA"; "OSSVerify.KrLib.LibA.ACnt24.cnt24"; "mm_fr"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "mul_mid_PHI"; "mul_mid_FR"; "mul_mid_SZ"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.A.A_mpi_journey2.rideA"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C2"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.A.A_mpi_journey.XDA"; "OSSVerify.KrLib.LibA.ARt.hstkhi"].


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


Definition A_WRAP_CALLOC_MM : Z := 0x68f10.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMCPY_MM : Z := 0x67848.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMSET_MM : Z := 0x67ce4.    (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mul_mid_PHI (dA dB : mpd) : Z := grow_PHI (md_n dA + md_n dB + 1).
Definition mul_mid_FR (d1 : Z) : Z := calls_FR 2 d1.

(* [comment removed for export] *)
Definition mul_mid_SZ (nX : Z) (dA dB : mpd) : Z := Z.max nX (Z.max (md_n dA + md_n dB) 1).

(* [comment removed for export] *)
Definition mm_fr (c0 c8 c16 c24 c32 c40 c48 c56 : word) : list cell := [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56].

Section WM.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CMUL : mpi_core_mul_stmtA asegs R HIA A_MPI_CORE_MUL.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_MM.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_MM.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_MM.
  (* [comment removed for export] *)
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (gp tp spv spe xs2 xs5 xs9 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd) (lo d1 : Z).
  Variable POST : config -> Prop.
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Local Notation SZB := (mul_mid_SZ nX dA dB).
  Hypothesis JC : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pc40,(4.&40.)Pc48,(4.&40.)Pc56,(4.&40.)(32.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R8.R7.R6.R5.R4.R3.R2.R1.))")
(* [comment removed for export] *).
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis D0 : 0 <= d1.
  Hypothesis NRA : 0 <= md_n dA <= 10000.
  Hypothesis NRB : 0 <= md_n dB <= 10000.
  Hypothesis NXA : md_addr dA <> X.
  Hypothesis NXB : md_addr dB <> X.
  Hypothesis SPE : bv_unsigned spv + 16 <= bv_unsigned spe.
  Hypothesis BUD : havol asegs R HIA h + mul_mid_PHI dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + mul_mid_FR d1 <= FR_MAX.
  Hypothesis SLO2 : lo <= bv_unsigned spv - 64 - 144 - arl_need_rt R.
  (* [comment removed for export] *)
  Hypothesis C24H : cnt24 LB + 2 <= C24MAX.

  Local Notation SP' := (Z_to_bv 64 (bv_unsigned spv + -64)).
  Local Notation SB := (Z_to_bv 64 (al_sb AL)).
  Local Notation XJF fr := (XJA asegs R HIA h LB LF m dX spv lo 64 fr []).
  Local Notation XJF1 fr An cnt := (XJA asegs R HIA h LB LF m dX spv lo 64 fr [(An, 4 * cnt)]).
  Local Notation FB0 := (FBA asegs R LB LF dX lo).
  Local Notation XDF fr := (XDA asegs R HIA h LB LF m dX spv lo 64 fr).
  Local Notation RIDE dE := (rideA R HIA LB LF m dX spv lo dE).
  Local Ltac jc_open c := pose proof (JC c c c c c c c c) as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Ltac xa_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1.

  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRAm; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 spv) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Definition KCL_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pr,$2.Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pc40,(4.&40.)Pc48,(4.&40.)Pc56,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pxa2,(4.&40.)Pxa3,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxs3,(4.&40.)Pxs4,(4.&40.)Pxs6,(4.&40.)Pxs7,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)(35.$1.)R25.R24.R23.R22.R21.R20.)P,(13.(15.$2.R20.=)(15.$2.R20.$36.))P,(19.R27.(37.VdA,VdB,))P,(19.R27.(38.Vd1,))P,(19.(1>.R24.)(39.VnX,VdA,VdB,))(3:.$2;.(3;.$2;.VR,VHIA,R28.Vmo,)VPOST,(3<.(3=.R1;.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R1:.R19.R18.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))R17.R16.R15.R14.R13.R12.R11.R10.Vxs2,R?.R>.Vxs5,R=.R<.(3>.&40.R24.)Vxs9,R;.R:.R9.R8.R7.R6.)VF,(3>.&40.+9>>4<.)Vfc,(3?.(4.&40.))R26.(40.$2;.)))")
(* [comment removed for export] *).
  Hypothesis KCL : KCL_stmt.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L18349620061.2000007S2dE2EB". (* [comment removed for export] *)
  #[using="Type"] Lemma rider_view : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "PdE,$6.Pv,$2.Pf,$2.Pfr,(0.$31.)Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.R5.(35.$1.)R7.R6.R4.R3.R2.R1.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,R9.R5.R4.R3.R2.)P,(11.(15.$2.(21.R:.)VX,))(14.(1?.$2;.R5.(21.R;.)(42.$31.(43.(3>.&40.(1:.R;.)))(42.$31.(44.(3>.&40.(27.R;.)))(42.$31.(44.(3>.&40.(1>.R;.)))(42.$31.(45.(28.R;.))(35.$31.))))))(14.(46.$2;.(47.VR,)(48.$2;.VR,VHIA,R7.)R5.(21.R;.)+10.)(14.(13.(15.$2.(27.R;.)+1.)(15.$2.(27.R;.)-1.))(14.(1;.=(21.R;.))(14.(19.(1<.(21.R;.)+10.)(2>.+2.+40.))(15.$2.(49.(21.R;.)+8.)=))))))")
(* [comment removed for export] *).
  Proof.
    intros dE v f fr hc LBc mc dXc J [E|[DBJ B]] NE; [exfalso; exact (NE E)|].
    pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B)) as [(CE & EAL & E0 & _) SGE]. unfold mpi_cells in CE.
    pose proof (rw_cells_bound _ _ _ _ CE) as EB. cbn [cells_size csize Nat.add] in EB.
    split; [exact CE|]. split; [exact (bj_aobj _ _ _ _ _ _ _ _ _ _ B)|]. split; [exact SGE|]. split; [exact E0|]. split; [clear - EB; lia| exact EAL].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01@0@D24976250634.176D24976250634.180D51099967397.176D51099967397.180D52014138856.176D52014138856.180K43355168775.178K43355168775.182L11385475062.1  L15466341142.171L29074168500.171L29074168500.175L35663928186.7  L43361613547.2  L43935804614.170L43935886280.171L43935886280.173L43937985922.168L46273107926.2  L49786828438.168L56464061078.2  L60098763854.3  L6503841302.169 P46286130337.177P46286130337.181P56460372320.178P56460372320.182Q13282358506.175Q13717524693.177Q1450055469.171 Q15641175235.172Q20498771212.176Q22053654841.172Q22055801988.175Q22055801988.176Q22285631880.175Q22285631880.179Q22286196081.174Q22287680565.172Q22288293173.176Q22288293174.178Q24267381591.177Q24974040330.177Q24974040330.181Q28027603798.174Q32655242887.174Q37374748791.174Q38735600301.176Q38737697513.174Q38738445840.177Q39212284437.175Q39212284437.177Q39212284437.179Q40066690834.172Q42081808994.175Q42081808994.179Q44648563964.171Q45402000102.176Q4926406185.175 Q4926406185.179 Q52016320488.177Q52016320488.181Q54208192516.172Q54253886744.174Q54255983967.178Q56761401107.175Q56761401107.179Q6027349519.176 Q6027349519.180 Q60511567613.175Q60511567613.177Q60511567613.179Q62495047012.175Q62965564504.176Q62965564504.180Q63229339625.172Q63229951721.176Q9538243134.174 Q9540340346.176 Q9540555642.172 00000W01>02F03N04504\05Q06L06Q06i07H07g08=08>08]09<09[0::0:;0:S0:T0:^0;60;70;80;90;:0;I0;X0<00<C0<R0<a0=00=?0=M0=[0=i0>70>E0>S0>e0?B0?e0@=0@P0@_0@n0A=0AL0A]0Al0B:0BR0Bf0C:0CM0C\0Cj0D80DU0E80EG0EU0Ec0F40FE0Fb0GE0GQ0G]0Gi0H;0HV0I10I?0IM0IY0Ie0J1S3spv1X3xs02dA2dB3dXc2fl2HB5Ha_st5Hl_stS3spv1X3xs02dA2dB3dXc2fl2HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO23dXc2fl5NEEDR3LOS2X03SPR2A02B02HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO23dXc2fl5NEEDR3LOS2X03SPR2A02B02HB5Ha_st5Hl_stS3spv1X3xs02dA2dB3dXc2fl2HB5Ha_st5Hl_stS3spv1X3xs02dA2dB3dXc2fl2HB5Ha_st5Hl_stS1R3spv1X3xs02lo4SLO23dXc2fl5NEEDR3DSX2HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO23dXc2fl5NEEDR3DSX2HB5Ha_st5Hl_stS3spvS3spv1X3xs02dA2dB3dXc2flS3spv1X3xs02dA2dB3dXc2fl2X03X16S3spv1X3xs02dA2dB3dXc2fl2X03X16S1R3HIA1h3spv2lo3TOP1HFS3spv1X3xs02dA2dB3dXc2fl2B03B16S3spv1X3xs02dA2dB3dXc2fl2A03A16S3spv1X3xs02dA2dB3dXc2fl2B03B16S3spv1X3xs02dA2dB3dXc2fl2A03A16FS3spv1X3xs02dA2dB3dXc2flFS1R2lo3LOSS3spv1X3xs02dA2dB3dXc2flFFFFS3xs02dA3dXc2flS3xs02dB3dXc2flS3spv3xs02lo3dXc2fl4LOSPS3spv3xs02lo3dXc2flS3xs02dB3dXc2flS3xs02dA3dXc2flS3xs02dA3dXc2flS3xs02dA3dXc2flS1X3xs03dXc2flS1X3xs03dXc2flS1X3xs03dXc2flS1X3xs03dXc2flS1X3xs03dXc2flS1X3xs03dXc2flS3xs02dB3dXc2fl2B0S1X3xs03dXc2fl2HB5Ha_st5Hl_stS1X3xs02dA2dB3dXc2fl2HB5Ha_st5Hl_stS3spv3xs02lo3dXc2fl4LOSPS3spv3xs02lo3dXc2flS3xs02dB3dXc2flS3xs02dB3dXc2flS3xs02dB3dXc2flS3xs02dB3dXc2flS1X3xs03dXc2fl2dAS3xs02dB3dXc2flS1X3xs03dXc2flS3spv3xs02lo3dXc2fl4LOSPS1X3xs03dXc2fl2X02HBS1X3xs03dXc2fl2X02HBS3spv3xs02lo3dXc2flS3xs02dA3dXc2flS1X3xs03dXc2flS1X3xs03dXc2flS1X3xs03dXc2fl2HB5Ha_st5Hl_stS1X3xs02dA2dB3dXc2fl2HB5Ha_st5Hl_stS3xs02dA3dXc2flS1X3xs03dXc2flS1X3xs03dXc2flS1X3xs03dXc2fl2X0S1X3xs03dXc2fl2X0S1X3xs03dXc2fl2HB5Ha_st5Hl_stS1X3xs02dA2dB3dXc2fl2HB5Ha_st5Hl_stS3xs03dXc2flS3xs03dXc2flS3xs03dXc2flS3xs02dA3dXc2fl2A0S1X3xs03dXc2fl3X162HB5Ha_stS1X3xs03dXc2fl3X162HB5Ha_stS1X3xs03dXc2flS1X3xs03dXc2flS3xs03dXc2flS3xs03dXc2flS3xs03dXc2fl". (* [comment removed for export] *)
  #[using="IMG JC NXA NXB SLO2 KCL"] Lemma mw_SIGN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pfl,(4.&40.)Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc48,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pxa2,(4.&40.)Pxa3,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxs6,(4.&40.)Pxs8,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R19.R18.R17.R16.R1:.(3>.&40.(1<.(21.VdB,)+8.))R15.(3>.&40.(1<.(21.VdA,)+8.)))(35.$1.)R20.R1?.R1>.R1=.R1<.R1;.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R1?.R1>.R1=.R1<.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R20.R1?.R1>.R1=.)P,(19.R23.(37.VdA,VdB,))P,(19.R23.(38.Vd1,))P,(19.(1>.R20.)(39.VnX,VdA,VdB,))(3:.$2;.(3;.$2;.VR,VHIA,R24.Vmo,)VPOST,(3<.(3=.R1:.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R19.R18.R17.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))R16.R15.R14.R13.R12.R11.R10.R?.Vxs2,(3>.&40.(1<.(4:.(1<.VX,+8.)+3.)(4;.(47.VR,))))(3>.&40.(4;.(47.VR,)))Vxs5,R>.(3>.&40.(1<.VX,+8.))R=.Vxs9,R<.R;.R:.R9.R8.R7.)VF,(3>.&40.+9>=;8.)Vfc,(3?.(4.&40.))R22.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J RA RB BV BF SZ. jc_open fl.
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ (JC fl fl fl fl fl fl fl fl)) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    destruct (rider_view _ _ _ _ _ _ _ _ J RA NXA) as (CEA & OEA & SGA & A0 & A16 & AAL).
    destruct (rider_view _ _ _ _ _ _ _ _ J RB NXB) as (CEB & OEB & SGB & B0 & B16 & BAL).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ (JC c0 c8 c16 c24 fl (Z_to_bv 64 (md_addr dB + 8)) c48 (Z_to_bv 64 (md_addr dA + 8))) _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof J as JX. xa_open JX. unfold mpi_cells in CX1. cbn [md_addr] in CX1, OX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in FR1, ST1 by (clear; lia).
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ (JC c0 c8 c16 c24 fl (Z_to_bv 64 (md_addr dB + 8)) c48 (Z_to_bv 64 (md_addr dA + 8))) _ _ _ _ _ _ _ J) as CWX. cbn [md_addr] in CWX. rewrite <- HT1 in CWX.
    pose proof (munch_refl [(X, X + 16)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KF0; zify_cond KF0.
    - (* [comment removed for export] *)
      zstep.
      shadow_chk OX1 (X + 8) 2.
      zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      match goal with H : HM asegs R HIA hc LBc LF m5 |- _ => rename H into HH5 end.
      pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ (JC c0 c8 c16 c24 fl (Z_to_bv 64 (md_addr dB + 8)) c48 (Z_to_bv 64 (md_addr dA + 8))) _ _ _ _ _ _ _ 1 J MU WM MI1 CX1 (or_introl eq_refl) HH5 OX1) as J5.
      eapply KCL; [exact J5| left; reflexivity| exact BV| exact BF| cbn [md_n]; exact SZ].
    - (* [comment removed for export] *)
      zstep.
      zstep. zstep. shadow_chk OEA (md_addr dA + 8) 2.
      zstep. zstep. zstep. shadow_chk OEB (md_addr dB + 8) 2.
      zstep. zstep. zstep.
      shadow_chk OX1 (X + 8) 2.
      zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      match goal with H : HM asegs R HIA hc LBc LF m5 |- _ => rename H into HH5 end.
      assert (SGP : md_sg dA * md_sg dB = 1 \/ md_sg dA * md_sg dB = -1) by (clear - SGA SGB; destruct SGA as [-> | ->]; destruct SGB as [-> | ->]; cbn; tauto).
      match goal with H : rw_cells asegs m5 X [C8 ?pp; C2 (Z_to_bv 64 ?a); ?nn; ?pd] |- _ =>
        pose proof (rw_cells_C2_congr asegs m5 X [C8 pp] a (md_sg dA * md_sg dB) [nn; pd] H
                      ltac:(clear - SGA SGB; destruct SGA as [-> | ->]; destruct SGB as [-> | ->]; vm_compute; reflexivity)) as CX5 end.
      cbn [app] in CX5.
      pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ (JC c0 c8 c16 c24 fl (Z_to_bv 64 (md_addr dB + 8)) c48 (Z_to_bv 64 (md_addr dA + 8))) _ _ _ _ _ _ _ (md_sg dA * md_sg dB) J MU WM MI1 CX5 SGP HH5 OX1) as J5.
      eapply KCL; [exact J5| left; reflexivity| exact BV| exact BF| cbn [md_n]; exact SZ].
    all: match goal with |- ?g => idtac "SIGN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0>L10510931130.3L11762681116.2L20422897925.4L20422899211.2L22961942245.0L25721262433.4L34389855963.2L39280637297.0L40362700714.0L53134459733.2L59031206751.1L59308585216.2L59308587280.2L59308666361.4L60451556164.300000900A00N00U00V00b00j00k00l01401801>01D01R01\S2dE1k2HKS2dE3EN1S1R2dE3ACV2HCS2dE2HISS2dE1k2HK2EZS3dXc2P0SSS2lo3LO0S2dES1a2HaS1q2HqS2dE1l4LENE2EZS2dE3dXc1K". (* [comment removed for export] *)
  #[using="JC"] Lemma rider_limbs : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "PdE,$6.Pv,$2.Pf,$2.Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pc40,(4.&40.)Pc48,(4.&40.)Pc56,(4.&40.)Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pk,$2.P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R=.R<.R;.R:.R9.R8.R7.R6.)(35.$1.)R?.R>.R5.R4.R3.R2.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,R11.R6.R5.R4.R3.)P,(11.(15.$2.(21.R12.)VX,))P,(15.$16.(17.R5.)$18.)P,(14.(19.=R5.)(19.R5.(1>.R14.)))(14.(4<.$2;.R8.(1:.R15.)(4=.(25.R15.)))(14.(15.$2.(4>.(24.(4.&40.)(25.R15.)))(1>.R15.))(14.(13.(19.(1<.(1:.R15.)(1=.+4.(1>.R15.)))(1:.R7.))(19.(1<.(1:.R7.)(1=.+4.(1>.R7.)))(1:.R15.)))(14.(15.$2.(49.(1:.R15.)+4.)=)(14.(13.(15.$2.R6.=)(1;.=(1:.R15.)))(14.(1;.(1<.(1:.R15.)(1=.+4.(1>.R15.)))(2>.+2.+40.))(14.(13.(19.(1<.(1:.R15.)(1=.+4.(1>.R15.)))Vlo,)(19.(>.&40.Vspv,)(1:.R15.)))(46.$2;.(47.VR,)(48.$2;.VR,VHIA,R:.)R8.(1:.R15.)(1=.+4.R6.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros dE v f c0 c8 c16 c24 c32 c40 c48 c56 hc LBc mc dXc k J [E|[DBJ B]] NE EO HK; [exfalso; exact (NE E)|].
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 c56) as JCc.
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
    pose proof (alloc_ceiling_val R) as ACV.
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HH1. cbn [app] in HH1.
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    destruct (limb_own_eq_dec (md_own dE) LNull) as [EN|EN].
    - destruct (OWNE0 EN) as [EP EZ]. rewrite EP, EZ.
      assert (EL : md_limbs dE = []) by (destruct (md_limbs dE); [reflexivity| exfalso; cbn [length] in LENE; clear - LENE EZ; lia]).
      rewrite EL. assert (K0 : k = 0) by (clear - HK EZ; lia). subst k.
      split; [unfold bytes_at; cbn [u32s flat_map length Z.of_nat]; split; [clear; lia|]; split; [clear; lia|]; intros q Hq; exfalso; clear - Hq; lia|].
      split; [reflexivity|]. split; [left; clear - P0; lia|]. split; [reflexivity|]. split; [left; reflexivity|]. split; [clear; lia|].
      split; [left; clear - LO0; lia|].
      split; [intros a Ha; exfalso; clear - Ha; lia| intros a Ha; exfalso; clear - Ha; lia].
    - ddestruct (OWNE1 EN) as (EN1 & EP0 & EPAL & EBY & ESK & BHP & BST).
      split; [exact EBY|]. split; [exact LENE|].
      split; [pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ B EO EN) as K; clear - K; lia|].
      split; [exact EPAL|]. split; [right; exact EP0|].
      split.
      { destruct (md_own dE) eqn:EOA; [exfalso; exact (EN eq_refl)| |].
        - destruct (BHP eq_refl) as [_ BINc]. destruct (hm_apart asegs R HIA hc LBc LF mc HH1) as [HBR _]. rewrite Forall_forall in HBR.
          destruct (HBR _ ltac:(apply in_app_iff; left; exact BINc)) as (_ & _ & HC & _). cbn [fst snd] in HC. clear - HC ACV. lia.
        - destruct (BST eq_refl) as [BRO|[_ BH]]; [| exact BH].
          destruct (A_mpi_copy.static_limbs_low (Z_to_bv 64 0) mc _ _ _ EBY LENE ltac:(clear - EN1; lia) BRO) as [_ HI]. clear - HI. lia. }
      split; [exact ESK|].
      eapply aobj_sub; [exact (bj_aobjL _ _ _ _ _ _ _ _ _ _ B EN)| clear; lia| clear - HK; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02^0@C17027589631.218C24110347431.219D42645876524.221D48913312823.221D56473130795.221D60111543915.221K11417992427.219K14258238712.221K21335155304.221K24907334969.221K28282495707.218K36717110276.218K50676525366.221K51734157276.221K61145032713.221K61715101887.221L10353688608.3  L11147441822.1  L11385475062.1  L11416546478.4  L122581036.14   L122682622.6    L124765098.12   L124779541.6    L1356673058.3   L1358740507.11  L1358770377.5   L14245130797.4  L14245754747.13 L14245788585.5  L14247885126.6  L14247885634.6  L18293330070.2  L19095841334.7  L21286346697.10 L21286346870.5  L21288348751.13 L21288444061.5  L21328277545.3  L21328728685.12 L21328735698.5  L21330669261.7  L21330832697.6  L21330862571.13 L21330944202.6  L21332961591.8  L23460843689.186L23597190194.10 L23597200269.3  L23599297382.4  L23599333300.11 L23643762344.11 L24902649530.13 L24902748776.5  L24902863260.7  L24903092123.6  L24904845955.6  L24904856892.12 L24905308024.3  L24908942950.8  L26761189766.2  L2747663505.4   L2747762755.11  L2749760634.4   L28270437390.5  L30544818878.11 L30544854636.3  L30546951815.5  L35069606260.8  L35071589612.5  L35663928186.7  L36715738693.2  L36759611408.4  L39024900950.5  L39025276581.4  L39025375863.12 L39027373646.4  L39040053931.7  L41937024693.8  L42633816569.1  L45270660533.4  L45272757598.3  L45645530228.5  L45645530228.9  L4732940365.3   L4732976287.11  L4735029017.10  L4735037606.4   L47795326877.12 L47795356495.4  L47797453732.4  L48358922032.7  L50082547513.9  L50092999479.7  L50093035493.15 L50095096796.7  L50095111267.13 L50416225425.8  L50416519067.9  L50429067642.7  L50429068158.7  L50429082817.12 L50430758502.7  L50431050978.10 L50431165333.7  L50431201095.15 L50671808483.4  L51284464315.187L51731989917.3  L52181964255.15 L53641223865.3  L54274957729.0  L57718672844.3  L58177949655.187L60013347957.5  L60098763854.3  L60283674290.13 L61140413322.13 L61140445016.6  L61141364444.4  L61142541751.6  L61142542259.5  L61711433322.4  L62400422047.5  L62402519156.5  L62402555046.12 L66151427842.16 L66151427842.17 L66990418839.186L6761270099.15  L6761280748.9   L6763377671.9   L6763411669.16  L6763723252.12  L6773895177.13  L9575550670.7   O13430056386.221O16576486960.221O17027589631.218O21778112569.221O22333905464.220O22333905464.221O24110347431.219O27575595071.218O43421534469.221O48089381257.221O57401407669.221P11417992427.219P14258238712.220P36717110276.218P61145032713.221Q10044758524.199Q10661382049.200Q1946824128.199 Q21750490675.199Q21750569356.200Q30215712839.221Q30987168515.200Q33478850983.200Q36646300200.200Q38250484404.221Q39095944126.200Q42645876524.221Q43877802600.221Q49058237960.200Q49433500843.200Q53113263298.199Q60807234163.200Q60976009979.200Q61264001456.200Q61264037391.199Q66375044744.200Q67329072568.199Q8222473558.200 00000100200_01P02c03Y03Z05906R07k08o0900:?0;U0=40>O0>Y0>^0>c0>d0>e0>f0>g0>h0>i0>j0>k0>l0>m0>n0>o0?00?80?F0?G0?H0?I0?J0?K0?L0?M0?\0?]0?^0?_0?`0@T0@U0@V0@W0@X0@l0@m0@n0A=0A>0A?0A@0AA0AB0AJ0AK0AY0AZ0A[0A\0A]0A^0An0Ao0BE0BF0BP0B]0B^0B_0B`0Ba0Bb0Bg0Bh0C10C?0CM0CN0CO0CP0CQ0CR0CS0CT0Cj0Ck0Cl0Cm0Cn0Co0DB0DC0DD0DE0DF0DG0DH0DI0DJ0DK0E80E90E`0Ej0Ek0F40Fa0G20G<0GV0GW0GX0GY0GZ0G[0G\0G]0G^0G_0H;0H<0I00I10I20I30I40I50I60IJ0IK0IL0IM0IN0IO0IP0IQ0IR0IS0IT0IU0IV0IW0IX0IY0J<0J=0J`0KC0Kf0LV0M^0M_0NB0Nh0Ni0OP0P:0P;0Q80Q[0Q\0Q]0R@0Rc0SF0Si0TcFFS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c243c48S3spv1X3xs02dA2dB1i1j3pXc2xs2fl2c02c83c163c243c48S1R3HIA1h3spv1X3xs02dA2dB2lo2hc3pXc2xs2fl2c02c83c163c243c483TOP2X03SPR2A02B03HT12P0S1R3spv1X3xs02dA2dB2lo3pXc2xs2fl2c02c83c163c243c483LOSFS1R3HIA2LF3spv3xs02dA2dB2lo1i1j2hc3LBc1N3pXc2xs2fl2c02c83c163c243c482HN3x144LENA4ASEP3x155POST0S1R3HIA2LF3spv3xs02dA2dB2lo1i1j2hc3LBc3pXc2xs2fl2c02c83c163c243c483x144LENB3BLS3x155POST0S1R3HIA2LF3spv3xs02dA2dB2lo1i1j2hc3LBc3pXc2xs2fl2c02c83c163c243c483x144LENA3ALS3x155POST0S1R3spv3xs02dA2dB2lo1i1j1N3pXc2xs2fl2c02c83c163c243c482HN3LOS3ALO2PCFS1R3spv3xs02dA2dB2lo4SLO21i1j1N3pXc2xs2fl2c02c83c163c243c482HN5NEEDR3LOS3ALO2PCS1R3HIA2LF3spv1X3xs02dA2dB2lo1i1j2hc3LBc3pXc2xs2fl2c02c83c163c243c483DSX3x143x155POST0S1R3HIA2LF3spv3xs02dA2dB2lo1i1j2hc3LBc1N3pXc2xs2fl2c02c83c163c243c482HN3x144LENB4BSEP3x155POST0S1R3HIA2LF3spv1X3xs02dA2dB2lo1i1j2hc3LBc1N3pXc2xs2fl2c02c83c163c243c482HN3x143XPc3x155POST0S2dA1i3HI_S3spvS3spvFFFFFFFFFFFFFS3spv2loS3spv1X2lo3DSXFFFFFFFS3spv2dB2lo3BLSFFFFS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c243c482A03A16FFFFS1X1i1j1N3pXc2HN3XPcFFS3spv2dA2lo3ALSFFFFFS3spv2loFS1i1j1N2HN3NR1FFFFFS1R1N3pXc2PC3ACVFS1R3HIA1h3spv2lo3TOP1HFS1i1j1N2HNS3spv3SPA3SPRFFFFFS3pXcFS2dB1j2HJS1i1j1N3pXc2HNS1i1j1N3pXc2HNFFFFFFFS2dA2dB1i1j3pXc3HI_2HJFFFFFS3spv2lo1N3pXc4XLScFFFFFFFFFS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c243c48FS1R3spv2lo4SLO21i1j1N3pXc2HN5NEEDR4XLScS2dA1i3HI_SS2dB1j2HJS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c243c48S1R3HIA1h3spv3TOPS1R2lo3LOSS3spv2lo1i1j1N3pXc2HN1a2NOFFFFFFFFFS3pXc2r04XPAL1q1r1H2H02q02H4FS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c243c482B03B16FFFFFFS1R3spv2lo4SLO24NRAmFFFFFFFFFFFFFFFS3xs02dA2dB2xs2fl2c02c83c163c243c48FS3xs02dA2dB2xs2fl2c02c83c163c243c48S3xs02dA2dB2xs2fl2c02c83c163c243c48S3xs02dA2dB2xs2fl2c02c83c163c243c48S3xs02dA2dB1i1j1N3pXc2xs2fl2c02c83c163c243c482HNS1R3spv3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c243c485NEEDR3LOS4SP643ALO3ACVFS3xs02dA2dB2xs2fl2c02c83c163c243c48S3xs02dA2dB2lo2xs2fl2c02c83c163c243c48FS3xs02dA2dB3pXc2xs2fl2c02c83c163c243c48S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c243c48FS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c243c482X02A02B03BAL2P0S3xs02dA2dB2xs2fl2c02c83c163c243c48FFS3xs02dA2dB2xs2fl2c02c83c163c243c48S3xs02dA2dB2xs2fl2c02c83c163c243c48S3xs02dA2dB2xs2fl2c02c83c163c243c48S3xs02dA2dB2xs2fl2c02c83c163c243c48S3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c243c482X02A03AAL2P0". (* [comment removed for export] *)
  #[using="IMG CMUL JC NXA NXB SLO2 KCL"] Lemma mw_CORE : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pi,$2.Pj,$2.Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pfl,(4.&40.)Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc48,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa1,(4.&40.)Pxa2,(4.&40.)Pxa3,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R14.R13.R12.R11.R15.(3>.&40.(1<.(21.VdB,)+8.))R10.(3>.&40.(1<.(21.VdA,)+8.)))(35.$1.)R1;.R1:.R19.R18.R17.R16.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R1:.R19.R18.R17.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R1;.R1:.R19.R18.)P,(15.$16.(17.R19.)$18.)P,(14.(19.=R21.)(19.R21.(1>.VdA,)))P,(14.(19.=R21.)(19.R21.(1>.VdB,)))P,(19.(1<.R23.R22.)(1>.R1<.))P,(19.R22.(37.VdA,VdB,))P,(19.R22.(38.Vd1,))P,(19.(1>.R1?.)(39.VnX,VdA,VdB,))(3:.$2;.(3;.$2;.VR,VHIA,R23.Vmo,)VPOST,(3<.(3=.R19.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R18.R17.R16.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))(3>.&40.(1:.R20.))R15.R14.R13.R12.R11.R10.R?.Vxs2,(3>.&40.(1<.(4:.(1<.VX,+8.)+3.)(4;.(47.VR,))))(3>.&40.(4;.(47.VR,)))Vxs5,(3>.&40.(21.VdB,))(3>.&40.(1<.VX,+8.))(3>.&40.(21.VdA,))Vxs9,(3>.&40.R27.)(3>.&40.R26.)R>.R=.R<.R;.)VF,(3>.&40.+9>=84.)Vfc,(3?.(4.&40.))R21.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J0 RA RB EO HI_ HJ HN BV BF SZ.
    pose proof (JC c0 c8 c16 c24 fl (Z_to_bv 64 (md_addr dB + 8)) c48 (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    destruct (rider_view _ _ _ _ _ _ _ _ J0 RA NXA) as (CEA & OEA & SGA & A0 & A16 & AAL).
    destruct (rider_view _ _ _ _ _ _ _ _ J0 RB NXB) as (CEB & OEB & SGB & B0 & B16 & BAL).
    destruct (rider_limbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i J0 RA NXA EO HI_) as (ABY & LENA & ASEP & PA4 & PAZ & A64 & ALS & OAL).
    destruct (rider_limbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j J0 RB NXB EO HJ) as (BBY & LENB & BSEP & PB4 & PBZ & B64 & BLS & OBL).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' own.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc. unfold mpi_cells in CX1.
    pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * (i + j)))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear - HN HI_ HJ; lia]).
    unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * (i + j)); (lo, bv_unsigned spv + -64)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    pose proof CMUL as SPC. unfold mpi_core_mul_stmtA, A_MPI_CORE_MUL in SPC.
    acallxA_sp (bv_unsigned spv + -64)
      (eapply SPC with (h := hc) (LB := LBc) (LF := LF) (X := pXc) (A := md_p dA) (an := i) (B := md_p dB) (bn := j) (lo := lo) (xs := xs) (ys := md_limbs dA) (zs := md_limbs dB);
       rewrite ?(unsigned_lit (bv_unsigned spv + -64)) by qlia;
       try eassumption; try reflexivity;
       first [ clear - HI_; lia
             | clear - HJ; lia
             | clear - HI_ HJ NRA NRB HN NR1; lia
             | rewrite LEN1; clear - HN; lia
             | rewrite LENA; clear - HI_; lia
             | rewrite LENB; clear - HJ; lia
             | rewrite LENA, LEN1; exact ASEP
             | rewrite LENB, LEN1; exact BSEP
             | clear - XPAL; Z.div_mod_to_equations; lia
             | rewrite LEN1; clear - PC ACP' P0 N1 ACV; lia
             | rewrite LENA; exact A64
             | rewrite LENB; exact B64
             | unfold MPI_CORE_MUL_STACK_A; clear - SLO2 NEEDR NRAm LOS; lia
             | rewrite HT1; clear - TOP; lia
             | clear - SPA SPR LOSP; lia
             | left; rewrite LEN1; clear - XLSc SLO2 NEEDR; lia
             | rewrite LEN1; clear - XLSc SLO2 NEEDR; lia
             | rewrite LENA; clear - ALS SLO2 NEEDR; lia
             | rewrite LENB; clear - BLS SLO2 NEEDR; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear - HN HI_ HJ; lia]
             | match goal with |- ?g => idtac "CMUL-PRE-LEFT:" g end ]).
    clear SPC.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMUL-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo (bv_unsigned spv + -64) |- _ => rename H into ST6 end.
    match goal with H : u32arr asegs m6 pXc ?l, H2 : length ?l = length xs |- _ => rename H into XARR6; rename H2 into LEN6; rename l into xs6l end.
    pose proof ST6 as ST6'.
    assert (HW6 : forall a, ~ outside [(pXc, pXc + 4 * (i + j)); (lo, bv_unsigned spv + -64)] a ->
                  (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned spv - 64).
    { intros a NO. cbn [outside] in NO.
      assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned spv - 64) by (clear - NO HN HI_ HJ; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH1 HW6
                  ltac:(cbn; split; [clear - XLSc SLO2 NEEDR HN HI_ HJ; lia| split; [clear; lia| exact I]])
                  ltac:(cbn; split; [clear - XPc HN HI_ HJ; lia| split; [clear - DSX SLO2 NEEDR; lia| exact I]]) XARR6
                  ltac:(exact LEN6)) as J6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
    pose proof (rideA_xl_munch R HIA h LB LF m dX spv lo 64 _ JCc dA _ _ _ _ _ _ pXc (pXc + 4 * (i + j)) xs6l m6 (bv_unsigned spv + -64) J0 RA eq_refl
                  ltac:(cbn [md_p]; clear; lia) ltac:(clear - HI_ HJ; lia) ltac:(cbn [md_p md_n]; clear - HN; lia) ltac:(clear; lia) MU WM) as RA6.
    pose proof (rideA_xl_munch R HIA h LB LF m dX spv lo 64 _ JCc dB _ _ _ _ _ _ pXc (pXc + 4 * (i + j)) xs6l m6 (bv_unsigned spv + -64) J0 RB eq_refl
                  ltac:(cbn [md_p]; clear; lia) ltac:(clear - HI_ HJ; lia) ltac:(cbn [md_p md_n]; clear - HN; lia) ltac:(clear; lia) MU WM) as RB6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in RA6, RB6.
    eapply mw_SIGN; [exact J6| exact RA6| exact RB6| exact BV| exact BF| cbn [md_n]; exact SZ].
    all: match goal with |- ?g => idtac "CORE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L1164172544.1 L46559357180.3L63782058157.300000300=00ES1XS1X2dE3SXBS1X2dE1K". (* [comment removed for export] *)
  #[using="JC"] Lemma ride_xstruct : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "PdE,$6.Pv,$2.Pf,$2.Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pc40,(4.&40.)Pc48,(4.&40.)Pc56,(4.&40.)Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pm',P,(4.&40.)(5.(4.&8.))PdXc',$6.P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R>.R=.R<.R;.R:.R9.R8.R7.)(35.$1.)R10.R?.R6.R5.R4.R3.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,R12.R7.R6.R5.R4.)P,(11.(15.$2.(21.R13.)VX,))P,(9.(42.(4?.$2.$2.)(50.$2.$2.VX,(1<.VX,+10.))(35.(4?.$2.$2.)))R7.R5.)P,(:.$2;.R8.R6.)P,(15.$16.(17.R6.)(17.R8.))P,(15.$2.(1:.R7.)(1:.R9.))P,(15.$2.(1>.R8.)(1>.R:.))(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,R19.R>.R=.R:.R9.)")
(* [comment removed for export] *).
  Proof.
    intros dE v f c0 c8 c16 c24 c32 c40 c48 c56 hc LBc mc dXc m' dXc' J [E|[DBJ B]] NE MU WM EO EP EN; [exfalso; exact (NE E)|].
    right. split; [exact DBJ|].
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 c56) as JCc.
    pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as OX. cbn [md_addr] in OX.
    pose proof DBJ as [_ OB _ _ SXB _]. destruct OB as (OB1 & _). cbn [md_addr] in OB1, SXB.
    assert (B2 : BJA asegs R HIA LF spv dE hc LBc m' dXc).
    { eapply bja_munch; [exact J| exact B| exact MU| exact WM| | |].
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX| apply Forall_nil].
      - cbn [disjoint_from]. split; [clear - SXB; lia| exact I].
      - intros BN. cbn [disjoint_from]. split; [pose proof (OB1 BN) as K; clear - K; lia| exact I]. }
    destruct B2 as [A1 A2 A3 A4 A5]. constructor; try assumption; rewrite ?EO, ?EP, ?EN; assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02H0@C17027589631.191C24110347431.192C26381392939.191C26381392939.192D24976250634.191D36455618899.190D51099967397.191D52014138856.191D64152481649.190D9829697447.193 K11417992427.192K25953536645.191K25953536645.192K28282495707.191K36717110276.191K50676525366.192K51734157276.192K53928659426.192K68655443531.192L10234651826.3  L10642801822.2  L11147441822.1  L11385475062.1  L11416546478.3  L13023482647.2  L1685717371.0   L18293330070.2  L18697651051.3  L19095841334.7  L23100341967.168L23100341967.180L23190362336.5  L23306501646.1  L23643762344.4  L24313534829.3  L24575809296.188L25939631124.2  L26761189766.2  L28270437390.4  L28457445181.2  L29074096193.180L29074168500.183L2975768925.2   L29763661393.2  L29765106966.167L33656807774.3  L33669198666.15 L34107323466.3  L35663928186.7  L35664669659.4  L35794219356.1  L36715738693.2  L38235734261.1  L38974215006.5  L39172636981.0  L41128898453.2  L41548176122.3  L42633816569.1  L43683357519.3  L43878034250.5  L45918878996.1  L46160487540.168L48154963340.182L48155162489.179L48349305323.4  L50416225425.15 L50430249489.4  L50671808483.3  L51601712534.168L51731989917.3  L52181964255.8  L5259801613.165 L53931073395.2  L54324727969.0  L54811923132.1  L54822575959.15 L58609956177.2  L60013347957.5  L60098763854.3  L60283674290.6  L6490717127.9   L68665096410.2  L8265267294.0   L8328083279.6   O13430056386.192O17027589631.191O24110347431.192O27575595071.191O57401407669.192P11417992427.192P25953536645.191P25953536645.192P36717110276.191Q10235026062.184Q12370813529.171Q17207350632.172Q17207432298.184Q18699268200.193Q22285631880.188Q22285648010.185Q22288293174.187Q22955808635.190Q24974040330.190Q2507926616.190 Q26207421841.172Q26207721832.173Q26207967338.170Q26295627581.187Q30215712839.193Q30987168521.173Q31654082872.172Q34054043951.172Q36453634899.191Q37625261960.170Q38250484404.193Q39212284437.173Q39212284437.188Q42081808994.188Q42631062289.187Q42631275027.184Q42643792741.187Q42645876524.193Q43877802600.193Q43925228937.173Q45054200725.187Q4926406185.188 Q51236026622.172Q52016320488.190Q53153893485.187Q54255983967.187Q54627523118.189Q5485126037.170 Q5485126037.184 Q5485174314.171 Q5485600919.172 Q56761401107.188Q59703481013.171Q6027349519.191 Q60511567613.173Q60511567613.188Q60697995187.173Q6143569392.171 Q62868926301.187Q62965564504.189Q63231501142.185Q64154756465.191Q66645058578.193Q68717453381.187Q8880503606.170 Q8943555749.184 Q9538787269.170 Q9538787269.185 00000100200300401101_03:04705205305405505605o06007407`08j09^09h09n0:30:80:90::0:;0:C0:M0:[0;D0<20<B0<G0<T0<_0=M0=N0=V0=W0=]0>R0?G0?N0?U0@D0@E0@]0@h0A>0A?0AD0AE0AI0A\0A]0A^0Ak0B00B=0BE0BH0C80D70E60ED0EW0EX0EY0FB0FC0Fc0GS0GT0GU0GV0Ge0Gl0H=0HG0HZ0I=0I>0I?0IQ0IR0IS0IT0IU0IV0IW0IX0IY0IZ0JE0K50KV0L<0Ld0MJ0N00NV0OE0P:0Pe0QF0Qg0RH0Rl0SQ0TU0U60Ua0VI0Vj0WL0Wm0XS0Y?0Yg0ZO0[70[Z0\@0\a0]I0]o0^U0_J0`50`[0aF0ag0bM0bn0cO0d80d90dn0eM0f10fU0g60ga0hT0i:0ie0jX0kC0kd0lH0lg0mKFFFFS3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242LQ2HB5Ha_st5Hl_stS3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242LQS1R3spv1X3xs02dA2dB2lo4SLO21N3pXc2xs2fl2c02c83c163c245NEEDR3LOS2X03SPR2P02LQ2HB5Ha_st5Hl_stS3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242LQ2HB5Ha_st5Hl_stS3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242X03SPR2N12P02LQFFFFS1R3spv3xs02dA2dB2lo1N3pXc2xs2fl2c02c83c163c243LOS3ALO2PCFS1R3spv3xs02dA2dB2lo4SLO21N3pXc2xs2fl2c02c83c163c245NEEDR3LOS3ALO2PCS3spv1X3xs02dA2dB2lo2xs2fl2c02c83c163c243DSXS1R3spv3xs02dA2dB2lo4SLO21N3pXc2xs2fl2c02c83c163c245NEEDR3LOS3ALO2N12PC2LQS1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242N12P03XPc2LQS1N3pXc2N1S1N2N1S3spvS3spvFFSS3spv2loS1N3pXc2N1S3spv1X2lo3DSXS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c24S3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242LQS1X1N3pXc2N13XPcS3pXcS1X1N3pXc3XPcS1N3pXc3P47S3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242LQFS3spv2loFS1N2N1S3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242X03X162LQS3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242X03X162LQS1N3pXcS1N3NR1S3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c243NR1FS1R3spv2lo4SLO24NRAm3SPRS1N2xs4LEN1S1R3HIA1h3spv2lo3TOP1HFS3pXcFS2loS3spv1X2lo4LOSP3DSXSFS3spv2lo4LOSPS3pXcS3spv2lo4LOSPS3spv2loS1NS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c242X03X16S3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242X03SPR2N12P03P472LQS3spv1X3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242X03SPR2N12P03P472LQS1N2xs4LEN12N1S3spv2lo1N3pXc4XLScFFS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c24FS1R3spv2lo4SLO21N3pXc5NEEDR4XLScS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c242X03X16FSFS3spv1N3SPR3NR1S1N3NR1S1R3HIA1h3spv3TOPS1R2lo3LOSS3spv2lo1N3pXc1a2NOS1R3spv2lo4SLO21N3pXc5NEEDR2N14XLScFSS2lo1N3pXc2N11a2NOFFFFFFFFFS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242N12LQS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c242X03XALS1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242N1S1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQS1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQS1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242N13P472LQS1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQ2HB5Ha_st5Hl_stS3xs02dA2dB2lo1N3pXc2xs2fl2c02c83c163c242LQS1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S3xs02dA2dB1N2xs2fl2c02c83c163c242LQS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c24S1R3spv3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDR3LOS4SP643ALO3ACPS1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242LQS1X3xs02dA2dB2xs2fl2c02c83c163c24S3xs02dA2dB2lo2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQS1X3xs02dA2dB1N2xs2fl2c02c83c163c242X02LQ2HBS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242LQS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242LQS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242LQS3xs02dA2dB3pXc2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242LQS1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQ2HB5Ha_st5Hl_stS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242P02LQS1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242P02LQS1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQS1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB1N2xs2fl2c02c83c163c242X02LQFS1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQ2HB5Ha_st5Hl_stS3xs02dA2dB2xs2fl2c02c83c163c24S3xs02dA2dB1N2xs2fl2c02c83c163c242LQS1X3xs02dA2dB2xs2fl2c02c83c163c242X0S1X3xs02dA2dB2xs2fl2c02c83c163c24S3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242N12LQS1X3xs02dA2dB1N2xs2fl2c02c83c163c243X162LQ2HB5Ha_stS1X3xs02dA2dB1N2xs2fl2c02c83c163c242LQS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242N12LQS1R3spv3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDRS3xs02dA2dB1N3pXc2xs2fl2c02c83c163c242N12LQS1X3xs02dA2dB2xs2fl2c02c83c163c24S3xs02dA2dB1N2xs2fl2c02c83c163c242LQS3xs02dA2dB2xs2fl2c02c83c163c24S3xs02dA2dB1N2xs2fl2c02c83c163c242LQ". (* [comment removed for export] *)
  #[using="IMG CMUL AMS JC NXA NXB SLO2 KCL"] Lemma mw_LSET : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pi,$2.Pj,$2.Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pfl,(4.&40.)Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxs3,(4.&40.)Pxs8,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R14.R13.R12.R11.R15.(3>.&40.(1<.(21.VdB,)+8.))(3>.&40.(21.VdA,))(3>.&40.(1<.(21.VdA,)+8.)))(35.$1.)R1;.R1:.R19.R18.R17.R16.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R1:.R19.R18.R17.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R1;.R1:.R19.R18.)P,(15.$16.(17.R19.)$18.)P,(14.(19.=R21.)(19.R21.(1>.VdA,)))P,(14.(19.=R21.)(19.R21.(1>.VdB,)))P,(19.(1<.R23.R22.)(1>.R1<.))P,(19.R22.(37.VdA,VdB,))P,(19.R22.(38.Vd1,))P,(19.(1>.R1?.)(39.VnX,VdA,VdB,))(3:.$2;.(3;.$2;.VR,VHIA,R23.Vmo,)VPOST,(3<.(3=.R1:.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R19.R18.R17.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))R16.R15.(3>.&40.(1<.(4:.(1<.VX,+:.)+3.)(4;.(47.VR,))))(3>.&40.(1<.VX,+:.))R14.R13.R12.R11.Vxs2,R10.(3>.&40.(4;.(47.VR,)))Vxs5,(3>.&40.(21.VdB,))(3>.&40.VX,)R?.Vxs9,(3>.&40.R27.)(3>.&40.R26.)R>.R=.R<.R;.)VF,(3>.&40.+9>=20.)Vfc,(3?.(4.&40.))R21.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J0 RA RB EO HI_ HJ HN BV BF SZ.
    pose proof (JC c0 c8 c16 c24 fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX; xa_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' own.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc. unfold mpi_cells in CX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as AB.
    unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * N); (lo, bv_unsigned spv + -64)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 N)) with (Z_to_bv 64 N)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_MM) as SPM. unfold A_ASAN_MEMSET_MM in SPM.
    acallxA_sp (bv_unsigned spv + -64)
      (eapply SPM with (h := hc) (LB := LBc) (LF := LF) (DST := pXc) (v := 0) (n := 4 * N) (lo := lo) (ds := u32s xs);
       rewrite ?(unsigned_lit (bv_unsigned spv + -64)) by qlia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMS; reflexivity
             | apply MpiWalkAux.u8arr_of_u32arr; exact XARR
             | rewrite u32s_length; clear - LEN1; lia
             | eapply aobj_sub; [exact OP| clear; lia| clear; lia]
             | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
             | eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]
             | rewrite HT1; clear - TOP; lia
             | f_equal; clear; lia
             | right; clear - P47; lia
             | clear - XLSc SLO2 NEEDR N1 NR1 NRAm LOS SPA SPR LOSP; lia
             | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]).
    clear SPM.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMSET-SIDE:" g end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo (bv_unsigned spv + -64) |- _ => rename H into ST6 end.
    match goal with H : u8arr asegs m6 pXc _ |- _ => rename H into HPZ end.
    match goal with H : HM asegs R HIA hc LBc LF m6 |- _ => rename H into HH6 end.
    replace (Z.to_nat (4 * N)) with (4 * Z.to_nat N)%nat in HPZ by (clear - N1; lia).
    apply (rw_cells_of_u8arr asegs) in HPZ.
    assert (XARR6 : u32arr asegs m6 pXc (repeat (Z_to_bv 64 0) (Z.to_nat N))).
    { eapply (u32arr_of_cells asegs); [exact HPZ| symmetry; apply u32s_repeat0]. }
    assert (HW6 : forall a, ~ outside [(pXc, pXc + 4 * N); (lo, bv_unsigned spv + -64)] a ->
                  (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned spv - 64).
    { intros a NO. cbn [outside] in NO.
      assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned spv - 64) by (clear - NO; lia).
      destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
    pose proof ST6 as ST6'.
    assert (LQ : length (repeat (Z_to_bv 64 0) (Z.to_nat N)) = length xs) by (rewrite repeat_length; clear - LEN1 N1; lia).
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ m6 _ J0 MU WM MI6 ST6' HH6 HW6
                  ltac:(cbn; split; [clear - XLSc SLO2 NEEDR; lia| split; [clear; lia| exact I]])
                  ltac:(cbn; split; [clear - XPc; lia| split; [clear - DSX SLO2 NEEDR; lia| exact I]]) XARR6
                  LQ) as J6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J6.
    pose proof (rideA_xl_munch R HIA h LB LF m dX spv lo 64 _ JCc dA _ _ _ _ _ _ pXc (pXc + 4 * N) (repeat (Z_to_bv 64 0) (Z.to_nat N)) m6 (bv_unsigned spv + -64) J0 RA eq_refl
                  ltac:(cbn [md_p]; clear; lia) ltac:(clear - N1; lia) ltac:(cbn [md_p md_n]; clear; lia) ltac:(clear; lia) MU WM) as RA6.
    pose proof (rideA_xl_munch R HIA h LB LF m dX spv lo 64 _ JCc dB _ _ _ _ _ _ pXc (pXc + 4 * N) (repeat (Z_to_bv 64 0) (Z.to_nat N)) m6 (bv_unsigned spv + -64) J0 RB eq_refl
                  ltac:(cbn [md_p]; clear; lia) ltac:(clear - N1; lia) ltac:(cbn [md_p md_n]; clear; lia) ltac:(clear; lia) MU WM) as RB6.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in RA6, RB6.
    (* [comment removed for export] *)
    clear MU WM CX1 OX1 HPZ J0 RA RB.
    try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear XP1; try clear XLS1; try clear NM1.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J6) as (_ & LEN6 & _ & _ & CX6 & _ & OWN6).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LEN6, CX6, OWN6. unfold mpi_cells in CX6.
    ddestruct (OWN6 ltac:(discriminate)) as (_ & _ & _ & _ & XARR6' & _ & _ & _ & OP6 & _).
    pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J6) as OX6. cbn [md_addr] in OX6.
    pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J6) as HH6'. cbn [app] in HH6'.
    pose proof (xa_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J6) as HT6.
    pose proof (xa_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J6) as FR6. unfold mm_fr in FR6. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in FR6 by (clear; lia).
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    pose proof (munch_refl [(pXc, pXc + 4); (lo, lo)] m6) as MU; pose proof (wmono_refl asegs m6) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OP6 pXc 4.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok asegs m6 pXc (repeat (Z_to_bv 64 0) (Z.to_nat N)) 0 _ XARR6' ltac:(rewrite repeat_length; clear - N1; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs m6 pXc (repeat (Z_to_bv 64 0) (Z.to_nat N)) 0 vv XARR6' ltac:(rewrite repeat_length; clear - N1; lia)) as XARR7 end.
    replace (pXc + 4 * 0) with (pXc + 0) in XARR7 by (clear; lia).
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with H : mem_inv asegs m7 |- _ => rename H into MI7 end.
    match goal with H : stk asegs m7 lo _ |- _ => rename H into ST7 end.
    match goal with H : HM asegs R HIA hc _ LF m7 |- _ => rename H into HH7 end.
    assert (HW7 : forall a, ~ outside [(pXc, pXc + 4); (lo, lo)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned spv - 64).
    { intros a NO. left. split; [reflexivity|]. cbn [outside] in NO. clear - NO N1. lia. }
    pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ m7 _ J6 MU WM MI7 ST7 HH7 HW7
                  ltac:(cbn; split; [clear - XLSc SLO2 NEEDR N1; lia| split; [clear - LOSP; lia| exact I]]) ltac:(cbn; split; [clear - XPc N1; lia| split; [clear - DSX LOSP; lia| exact I]]) XARR7
                  ltac:(rewrite upd_length; reflexivity)) as J7.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J7.
    pose proof (rideA_xl_munch R HIA h LB LF m dX spv lo 64 _ JCc dA _ _ _ _ _ _ pXc (pXc + 4) (upd (repeat (Z_to_bv 64 0) (Z.to_nat N)) (Z.to_nat 0) (Z_to_bv 64 0)) m7 lo J6 RA6 eq_refl
                  ltac:(cbn [md_p]; clear; lia) ltac:(clear; lia) ltac:(cbn [md_p md_n]; clear - N1; lia) ltac:(clear - LOSP; lia) MU WM) as RA7.
    pose proof (rideA_xl_munch R HIA h LB LF m dX spv lo 64 _ JCc dB _ _ _ _ _ _ pXc (pXc + 4) (upd (repeat (Z_to_bv 64 0) (Z.to_nat N)) (Z.to_nat 0) (Z_to_bv 64 0)) m7 lo J6 RB6 eq_refl
                  ltac:(cbn [md_p]; clear; lia) ltac:(clear; lia) ltac:(cbn [md_p md_n]; clear - N1; lia) ltac:(clear - LOSP; lia) MU WM) as RB7.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in RA7, RB7.
    (* [comment removed for export] *)
    clear MU WM J6 RA6 RB6. try clear CX6; try clear OX6; try clear XARR6'; try clear XARR7; try clear OP6; try clear HH6'; try clear FR6.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J7) as (_ & _ & _ & _ & CX7 & _ & _).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX7. unfold mpi_cells in CX7.
    pose proof (xa_aobjX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J7) as OX7. cbn [md_addr] in OX7.
    pose proof (xa_cwX _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J7) as CWX. cbn [md_addr] in CWX. rewrite <- HT6 in CWX.
    pose proof (munch_refl [(X, X + 16)] m7) as MU; pose proof (wmono_refl asegs m7) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX7 (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
    match goal with H : mem_inv asegs m8 |- _ => rename H into MI8 end.
    match goal with H : HM asegs R HIA hc LBc LF m8 |- _ => rename H into HH8 end.
    match goal with H : aobj asegs AL (hcs asegs R HIA hc) m8 X 16 |- _ => rename H into OX8 end.
    match goal with H : rw_cells asegs m8 X _ |- _ => rename H into CX8 end.
    pose proof (xa_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ 1 J7 MU WM MI8 CX8 (or_introl eq_refl) HH8 OX8) as J8.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J8.
    pose proof (ride_xstruct dA _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 (mkMPD X 1 N pXc (upd (repeat (Z_to_bv 64 0) (Z.to_nat N)) (Z.to_nat 0) (Z_to_bv 64 0)) padX LHeap) J7 RA7 NXA MU WM eq_refl eq_refl eq_refl) as RA8.
    pose proof (ride_xstruct dB _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 (mkMPD X 1 N pXc (upd (repeat (Z_to_bv 64 0) (Z.to_nat N)) (Z.to_nat 0) (Z_to_bv 64 0)) padX LHeap) J7 RB7 NXB MU WM eq_refl eq_refl eq_refl) as RB8.
    eapply (mw_CORE i j _ _ _ _ _ (mkMPD X 1 N pXc (upd (repeat (Z_to_bv 64 0) (Z.to_nat N)) (Z.to_nat 0) (Z_to_bv 64 0)) padX LHeap)); [exact J8| exact RA8| exact RB8| reflexivity| exact HI_| exact HJ| cbn [md_n]; exact HN| exact BV| exact BF| cbn [md_n]; exact SZ].
    all: match goal with |- ?g => idtac "LSET-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L11101949.5   L17665107458.7L22961942245.0L39280637297.0L41707467178.1L48191417473.5L52419075592.0L59308587280.200000C00\00]00^00c01501601<S3spv1X2lo4LOSP3DSXS3spv2lo3dXc4LOSP4LEN12XLSSS3spvS3spv2lo4LOSP1a2NOSS1q2Hq". (* [comment removed for export] *)
  #[using="JC"] Lemma xa_fr_store : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "PEX,(0.$1.)Pv,$2.Pf,$2.Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pc40,(4.&40.)Pc48,(4.&40.)Pc56,(4.&40.)Pk0,(4.&40.)Pk8,(4.&40.)Pk16,(4.&40.)Pk24,(4.&40.)Pk32,(4.&40.)Pk40,(4.&40.)Pk48,(4.&40.)Pk56,(4.&40.)Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pm',P,(4.&40.)(5.(4.&8.))P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R15.R14.R13.R12.R11.R10.R?.R>.)R18.R17.R16.R5.R4.R3.R2.)P,(9.(42.(4?.$2.$2.)(50.$2.$2.(1<.(>.&40.Vspv,)-40.)(>.&40.Vspv,))(35.(4?.$2.$2.)))R4.R2.)P,(:.$2;.R5.R3.)P,(;.$2;.R4.)P,(<.$2;.R5.Vlo,(1<.(>.&40.Vspv,)-40.))P,(?.$2;.VR,VHIA,R:.(10.$1.R1=.R9.)VLF,R6.)P,(1?.$2;.R7.(1<.(>.&40.Vspv,)-40.)(34.R13.R12.R11.R10.R?.R>.R=.R<.))(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R14.R13.R12.R11.R10.R?.R>.R=.)R1?.R1>.R1=.R<.R;.R8.R9.)")
(* [comment removed for export] *).
  Proof.
    intros until m'. intros J MU WM MI' ST' HH' FR'.
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 c56) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    pose proof (xa_XLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as XLS1.
    replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) in ST', FR', MU by (clear; lia).
    assert (ARR' : u32arr asegs m' (md_p dXc) (md_limbs dXc)).
    { destruct (limb_own_eq_dec (md_own dXc) LNull) as [EO|NEO].
      - ddestruct (OWN0 EO) as (EP & EN & EL). rewrite EP, EL. unfold u32arr, bytes_at, wr_at. cbn [u32s flat_map length Z.of_nat Z.mul].
        split; (split; [clear; lia| split; [clear; lia| intros q Hq; exfalso; clear - Hq; lia]]).
      - ddestruct (OWN1 NEO) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
        eapply (u32arr_transport asegs [(bv_unsigned spv - 64, bv_unsigned spv)] mc m'); [exact XARR| exact MU| exact WM|].
        cbn [disjoint_from]. split; [| exact I]. pose proof (XLS1 NEO) as XL. clear - XL LEN1 LOSP N1. lia. }
    pose proof (xa_limbs_fr asegs R HIA h LB LF m dX spv lo 64 _ (mm_fr k0 k8 k16 k24 k32 k40 k48 k56) JCc _ _ _ _ _ _ _ _ m' (md_limbs dXc) J MU WM MI' ST' HH'
                  ltac:(intros a NO; right; cbn [outside] in NO; clear - NO LOSP; lia) FR'
                  ltac:(cbn [disjoint_from md_addr]; split; [clear - DSX LOSP; lia| exact I]) ARR' eq_refl) as J'.
    destruct dXc. exact J'.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L14941169057.5L50547719289.5L51462270997.8L7182566951.5 00000C00W00n01AS3spv2lo2dE4LOSP2ESS3spv2lo2dE4LOSP3EL5S1R3HIA1h3spv3TOP5HTOP0S1R3spv2lo3LOS4LOSP". (* [comment removed for export] *)
  #[using="JC"] Lemma ride_fr_store : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "PdE,$6.PEX,(0.$1.)Pv,$2.Pf,$2.Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pc40,(4.&40.)Pc48,(4.&40.)Pc56,(4.&40.)Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pm',P,(4.&40.)(5.(4.&8.))P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R=.R<.R;.R:.R9.R8.R7.R6.)R10.R?.R>.R5.R4.R3.R2.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,R12.R6.R5.R4.R3.)P,(9.(42.(4?.$2.$2.)(50.$2.$2.(1<.(>.&40.Vspv,)-40.)(>.&40.Vspv,))(35.(4?.$2.$2.)))R5.R3.)P,(:.$2;.R6.R4.)(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,R15.R9.R8.R5.R6.)")
(* [comment removed for export] *).
  Proof.
    intros dE EX v f c0 c8 c16 c24 c32 c40 c48 c56 hc LBc mc dXc m' J [E|[DBJ B]] MU WM; [left; exact E| right; split; [exact DBJ|]].
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 c56) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HS1.
    pose proof (hcs_stack asegs R HIA hc) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP0.
    eapply bja_munch; [exact J| exact B| exact MU| exact WM| | |].
    - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS0| clear - LOS LOSP; lia| rewrite HS1; clear - HTOP0 TOP LOSP; lia]| apply Forall_nil].
    - cbn [disjoint_from]. split; [clear - ES LOSP; lia| exact I].
    - intros BN. cbn [disjoint_from]. split; [ddestruct (OWNE1 BN) as (_ & _ & _ & _ & EL5 & _); clear - EL5 LOSP; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation SH10 := (Z_to_bv 64 (Z.shiftr (X + 10) 3 + al_sb AL)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00W0@D24976250634.162D51099967397.162D51099967397.163D52014138856.162D52014138856.163D62155808737.163K35927268873.163K38856059124.163L23100341967.157L35928849865.9  L38869592309.3  L46160487540.157L49578233423.157L5262209306.156 P38856059124.163Q12370813529.160Q17205055869.159Q24974040330.162Q26207421841.159Q26207721832.160Q26207967338.157Q31654082872.159Q37623376543.159Q39212284437.160Q42081808994.160Q43925228937.160Q52016320488.162Q5483308162.159 Q5485174314.160 Q6027349519.162 Q6027349519.163 Q60511567613.160Q60697995187.160Q6143569392.160 Q62157788641.162Q62965564504.161Q7891539809.160 Q8880503606.157 Q9538787269.157 00000k02A03S04N05E06<07O07P08808908:08i09Q0:@0:A0;00;Q0<E0<f0=G0=h0>I0>j0?K0@20@S0AJ0Ak0BL0C@0D30DR0E60EW0FJ0G80G_0H@0H_S3spv1X3xs02dA2dB3cnt2An2ys2fl2c02c83c163c242HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO23cnt2An2ys2fl2c02c83c163c245NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO22An2ys2fl2c02c83c163c245NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS3spv1X3xs02dA2dB3cnt2An2ys2fl2c02c83c163c242HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2An2ys2fl2c02c83c163c242HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2An2ys2fl2c02c83c163c242HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO23cnt2ys2fl2c02c83c163c245NEEDR3FSZ3DSX2HB5Ha_st5Hl_st2AnFS3spv1X3xs02dA2dB2An2ys2fl2c02c83c163c24FFS3spv1X3xs02dA2dB2An2ys2fl2c02c83c163c242X03X16S3spv1X3xs02dA2dB2An2ys2fl2c02c83c163c24S3spv1X3xs02dA2dB2An2ys2fl2c02c83c163c242X03X16FS3spv1X3xs02dA2dB2An2ys2fl2c02c83c163c242X03XALS1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB3cnt2ys2fl2c02c83c163c242HB5Ha_st5Hl_stS1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB2ys2fl2c02c83c163c242X02HBS1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB3cnt2ys2fl2c02c83c163c242HB5Ha_st5Hl_st2AnS1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB3cnt2ys2fl2c02c83c163c242HB5Ha_st5Hl_stS1X3xs02dA2dB2An2ys2fl2c02c83c163c242HB5Ha_st5Hl_stS3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB2ys2fl2c02c83c163c242X0S1X3xs02dA2dB2ys2fl2c02c83c163c24S1X3xs02dA2dB2An2ys2fl2c02c83c163c242HB5Ha_st5Hl_stS1X3xs02dA2dB2ys2fl2c02c83c163c243X162HB5Ha_stS1X3xs02dA2dB2ys2fl2c02c83c163c242X02HBS1X3xs02dA2dB2ys2fl2c02c83c163c24S3xs02dA2dB2ys2fl2c02c83c163c24". (* [comment removed for export] *)
  #[using="IMG CMUL AMS JC NXA NXB SLO2 KCL"] Lemma mw_GFIN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pi,$2.Pj,$2.Pcnt,$2.Pv,$2.Pf,$2.Phd,(3.$2;.VR,VHIA,)PLBd,(0.$1.)PAn,$2.Pys,(0.(4.&40.))Pme,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pfl,(4.&40.)Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa1,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxs8,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(51.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R12.R11.R10.R?.R13.(3>.&40.(1<.(21.VdB,)+8.))(3>.&40.(21.VdA,))(3>.&40.(1<.(21.VdA,)+8.)))R1;.R1:.R19.R18.R17.R1<.R16.R15.R14.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R1:.R19.R16.R15.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R1;.R1:.R17.R16.)P,(14.(19.=R21.)(19.R21.(1>.VdA,)))P,(14.(19.=R21.)(19.R21.(1>.VdB,)))P,(19.(1<.R23.R22.)R21.)P,(19.R21.(37.VdA,VdB,))P,(19.R21.(38.Vd1,))P,(19.R24.(39.VnX,VdA,VdB,))(3:.$2;.(3;.$2;.VR,VHIA,R22.Vmo,)VPOST,(3<.(3=.R17.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R16.R15.R14.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))(3>.&40.R20.)R13.(3>.&40.(1<.(4:.(1<.VX,+:.)+3.)(4;.(47.VR,))))(3>.&40.(1<.VX,+:.))R12.R11.R10.R?.Vxs2,(3>.&40.R25.)(3>.&40.(4;.(47.VR,)))Vxs5,(3>.&40.(21.VdB,))(3>.&40.VX,)R>.Vxs9,(3>.&40.R27.)(3>.&40.R26.)R=.R<.R;.R:.)VF,(3>.&40.+9>=00.)Vfc,(3?.(4.&40.))R1>.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros D4 RA4 RB4 HI_ HJ HN BV BF CSZ.
    pose proof (JC c0 c8 c16 c24 fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hd.
    pose proof D4 as [DMI DST4 DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN4 DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in DCX, DOX, DHM. unfold mpi_cells in DCX.
    pose proof (hm_top asegs R HIA hd _ LF me DHM) as HTOP4.
    pose proof (AIh_laws asegs R HIA hd) as LAWS. pose proof (KF_kinv asegs R HIA hd mo) as KINV.
    pose proof (xda_cwX _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ _ D4) as CW5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CW5.
    rewrite <- DHT in CW5.
    pose proof (munch_refl [(X, X + 16)] me) as MU. pose proof (wmono_refl asegs me) as WM.
    (* [comment removed for export] *)
    shadow_chk DOX (X + 10) 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
    pose proof (xda_finish _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ _ _ _ D4 MU WM MI5 DCX DHM DOX) as J5.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
    pose proof (rideA_finish R HIA h LB LF m dX spv lo 64 _ JCc dA _ _ _ _ _ _ _ _ _ _ D4 RA4 MU WM) as RA5.
    pose proof (rideA_finish R HIA h LB LF m dX spv lo 64 _ JCc dB _ _ _ _ _ _ _ _ _ _ D4 RB4 MU WM) as RB5.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in RA5, RB5.
    eapply (mw_LSET i j _ _ _ _ _ (mkMPD X (md_sg dXc) cnt An ys padX LHeap)); [exact J5| exact RA5| exact RB5| reflexivity| exact HI_| exact HJ| cbn [md_n]; exact HN| exact BV| exact BF| cbn [md_n]; exact CSZ].
    all: match goal with |- ?g => idtac "GFIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation UWC mc := (uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned spe) (bv_unsigned spv) d1).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L1000762305.4 L52101693566.6L62037129548.600000A00S00kS3spv2lo3LO04LOSPS1R3HIA1h3spv1a2HaS1R3spv2lo4LOSP4SP643LOS". (* [comment removed for export] *)
  #[using="LB LF m X sX nX pX xs0 padX ownX lo JC"] Lemma uwc_fr_store : forall mc m', UWC mc -> munch [(bv_unsigned spv + -64, bv_unsigned spv)] mc m' -> UWC m'.
  Proof.
    intros mc m' UW MU. pose proof (JC spv spv spv spv spv spv spv spv) as JCc.
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & _).
    pose proof (jca_LOS _ _ _ _ _ _ _ _ _ _ _ _ JCc) as LOS.
    eapply uwc_munch; [exact UW| exact MU| clear - LO0 LOSP; lia| apply hstkhi_le64; clear - LOS LOSP SP64; lia|].
    intros a Ha. cbn [outside]. split; [clear - Ha; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac shadow_merge_keys2_a c k HK pk pt :=
    lazymatch goal with
    | |- aevtA ?segs _ _ (MS ?Rg ?Fg (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fcg ?rv ?mg ?ro) =>
        merge_cut_apply segs (fun ms' => exists vk vt : word, ms' = MS (tset pt vt (tset pk vk Rg)) Fg (Z_to_bv 64 fast) fcg rv mg ro);
        [ let Kz := fresh "Kz" in
          if_cases Kz; zify_cond Kz;
          [ shadow_merge_slow c k HK Kz; apply evtA_done; eexists; eexists; reflexivity
          | apply evtA_done; eexists; eexists; reflexivity ]
        | let ms' := fresh "ms'" in let vk := fresh "vk" in let vt := fresh "vt" in
          intros ms' (vk & vt & ->); cbv beta iota delta [tset]; try clear HK; try clear k ]
    end.
  Tactic Notation "shadow_merge_regs2_a" constr(c) constr(k) constr(HK) constr(nk) constr(nt) :=
    let pk := eval vm_compute in (bv_key (Z_to_bv 5 nk)) in
    let pt := eval vm_compute in (bv_key (Z_to_bv 5 nt)) in
    shadow_merge_keys2_a c k HK pk pt.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03n0@C17027589631.263C17027589631.264C17027589631.265C53523983875.266C53523983875.267D13554616751.168D13554616751.169D13554616751.229D2000233302.199 D2000233302.201 D2012999159.288 D2012999159.289 D2012999159.294 D22468532914.267D35664270806.287D35664270806.295D40944481165.201D40948596012.293D4209699008.267 D50818716548.168D50818716548.169D57950589477.229D60111543915.267D61202370633.293D7342806496.267 D936947614.267  K12565428082.229K1327100147.266 K1327100147.267 K2610174859.265 K2610174859.267 K36717110276.263K36717110276.264K36717110276.265K42587433812.168K42587433812.169K42587433812.229K50418191556.265K50418191556.267L1000762305.4   L10081841430.219L10081841430.281L11147441822.1  L11385475062.1  L12553287539.3  L12755534717.10 L12755534717.9  L1342025005.3   L13642019862.164L13642019862.212L13642019862.220L13642019862.281L13882674122.5  L13983990909.4  L14748712526.18 L14751320984.1  L14760987928.8  L16473205958.6  L16473494895.4  L17585880332.14 L17971934183.36 L18293330070.2  L20803911415.2  L21004385536.6  L2166243551.4   L22479292268.1  L23073757250.9  L23100341967.212L23100341967.251L23615739305.3  L24313534829.3  L24313585860.4  L24313813357.7  L25044269509.2  L25046775673.250L25047280258.218L25444354594.13 L2607826517.4   L26950159893.14 L27481632834.8  L27481632834.9  L27954469902.3  L28655862141.3  L29276612500.4  L32879090465.0  L33656307740.18 L33656807774.3  L33668935836.36 L33669198666.8  L34412813842.39 L34424803280.3  L35655538624.7  L35655538630.7  L35663928186.7  L35664646770.5  L36200541390.10 L36715738693.2  L37727358070.164L38033934840.14 L38235734261.1  L39025421106.1  L39039957623.36 L39039957623.39 L39172636981.0  L39372408534.39 L39436426759.7  L40449602357.4  L41389564045.11 L41707467178.1  L4195179459.5   L42594106808.2  L42602157212.1  L43625157983.1  L43631939593.39 L43878034250.5  L43995781104.3  L45904660944.18 L45905086801.4  L45917157712.39 L45917420166.10 L46160487540.219L46225601430.163L46225601430.212L46225601430.281L46756382136.212L46948640662.39 L4762891152.4   L47760128357.7  L47834816178.4  L48154966246.212L49764284278.219L49807695752.8  L50416225425.8  L50428288129.4  L50671808483.3  L5098421631.4   L51653596439.201L5259801613.211 L536504997.36   L53812879153.36 L547707976.3    L54980800062.1  L55785555446.163L56689323830.295L59308633593.3  L59308972243.3  L59321342598.4  L60013347957.5  L60098763854.3  L61202552813.5  L61562785068.36 L62018535662.1  L62030908141.6  L62825694812.4  L64811930313.11 L64934269637.2  L66661851587.4  L67380509172.4  L67601363691.1  L9951453048.12  O17027589631.263O17027589631.264O17027589631.265O22985009913.265O22985009913.267O33748860092.267O37541396745.263O37541396745.264O37541396745.265O45220981399.265O45220981399.267O53523983875.266O53523983875.267P1327100147.266 P1327100147.267 P27967082900.229P36717110276.263P36717110276.264P36717110276.265P40435166955.263P40435166955.264P40435166955.265P44002314798.267Q11801279589.168Q11801279589.169Q11801279589.229Q12370813529.216Q12370813529.260Q15457446739.165Q15457446739.166Q15457446739.226Q17207432298.215Q17207432298.259Q18363828416.165Q18365979785.226Q18366170748.215Q18366170748.291Q22468532914.267Q25513505925.167Q25513505925.168Q25513505925.228Q26207421841.225Q26207721832.226Q26207967338.259Q26210080640.223Q30985055127.188Q30985055127.284Q30985135241.247Q30987329587.266Q30987329589.170Q31653536963.259Q31654082872.225Q37625261960.215Q37625261960.259Q38250484404.267Q39212284437.226Q41152143740.225Q41152143740.291Q4209699008.267 Q43877802600.267Q43925228937.226Q49698585326.166Q49698585326.167Q49698585326.227Q50671937458.293Q52105658541.225Q52105658541.291Q52182444307.200Q52186720178.290Q52186720178.291Q52186720178.292Q5485126037.215 Q5485126037.259 Q5485174314.216 Q5485174314.260 Q58132722221.164Q58132722221.215Q58132722221.291Q59842863100.164Q59842863100.215Q59842863100.291Q60511567613.226Q60697995187.226Q6143569392.216 Q6143569392.260 Q64139569937.165Q64141419949.215Q64141419949.291Q64141885272.226Q7377275490.167 Q7377275490.168 Q7377275490.228 Q8882648284.223 Q9540835375.223 00000100200300400501D02S04004104204304404505305405505Z06S07g0950:C0;L0<S0<T0<U0=d0?A0?B0?C0@G0AK0AL0AM0AN0BZ0Cf0E10FB0GS0Gd0HP0II0IN0IS0IT0IU0IV0IW0J<0Jd0KP0LI0LY0Li0M:0M;0M<0MP0MQ0MR0Mc0Mk0Ml0ND0NT0NX0Nm0OU0PE0PO0P\0P]0P^0Pg0Q_0RS0S00S10S20S30S40S50S60SF0SG0S_0S`0T70T80TG0TH0Td0U@0UV0UW0UX0UY0V>0Vk0Vo0W00W=0WJ0WK0X10XG0XH0XI0XN0X^0X_0Xd0Xe0YA0YI0YJ0Y]0Y^0Z10Z20Ze0[J0\20\k0^K0_;0_G0_\0_n0_o0`[0`\0a10a20a30aK0b00b_0cH0ca0ck0d00dU0eN0eY0ed0ee0f60f@0fA0g10g40gL0gM0gd0gm0h=0hN0hS0hT0hU0hV0hW0hX0hY0hZ0h[0h\0h]0h^0h_0h`0ha0hb0hc0jC0jD0jE0jF0kM0lT0m[0o70om10a11V12E13<13b14H14n15O16416Z17@17f18Y19M1:F1;=1<51<V1=71=\1>=1?A1@R1Ak1C<1D@1De1EF1Eg1FL1G@1Ga1HG1I:1J61Jn1KO1L@1M11Mb1O11O\1PT1PU1PV1PW1PX1Q91Q^1R?1Rd1SO1T:1U21UX1V>1W11WP1X41XU1Y:1Ye1ZP1[H1\31]11]m1^j1_K1_jFFFFFS1R3spv1X3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO23pXc2xs2fl2c02c83c163c245NEEDR3LOS2X03SPR2An3An02P02HB5Ha_st5Hl_stFFFFFS3spv1X3xs02dA2dB3cnt3nXc3pXc2xs2fl2c02c83c163c242An4SLEN4DLENFFS3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv1X3xs02dA2dB3cnt3nXc3pXc2xs2fl2c02c83c163c242An4ZLENS3spv1X3xs02dA2dB3cnt3nXc3pXc2xs2fl2c02c83c163c242X03SPR2An3An02N12P04Fcnt4SLEN4DLENS1R3HIA1h3spv1X3xs02dA2dB2hc2xs2fl2c02c83c163c243TOP2X03SPR3HT12HB5Ha_st5Hl_stS1R3HIA1h3spv1X3xs02dA2dB2hc2xs2fl2c02c83c163c243TOP2X03SPR3HT12HB5Ha_st5Hl_stS1R3HIA3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c242h22An4TOP22HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo3cnt3nXc3pXc2xs2fl2c02c83c163c243LOS2An4SLEN4DLENFFS1R3HIA3spv1X3xs02dA2dB2lo3cnt3nXc3pXc2xs2fl2c02c83c163c242An2h24TOP24SLEN4DLENS1R3spv3xs02dA2dB2lo4SLO23nXc3pXc2xs2fl2c02c83c163c245NEEDR3LOS3ALO4LEN12An2PC2HB5Ha_st5Hl_stFFS3xs02dA2dB3cnt3nXc3pXc2xs2fl2c02c83c163c244LEN12An2N14SLEN4DLEN3SEPS3xs02dA2dB3cnt3nXc3pXc2xs2fl2c02c83c163c244LEN12An2N14SLEN4DLEN3SEPFFFS1R3spv1X3xs02dA2dB2lo4SLO23pXc2xs2fl2c02c83c163c245NEEDR3DSX2HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO23pXc2xs2fl2c02c83c163c245NEEDR3DSX2HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDR3DSX2An2HB5Ha_st5Hl_stS1R3spv3xs02dA2dB2lo3cnt3nXc3pXc2xs2fl2c02c83c163c243LOS3ALO4LEN12N12PC4SLEN4DLENS1R3spv3xs02dA2dB2lo3cnt3nXc3pXc2xs2fl2c02c83c163c243LOS3ALO4LEN12N12PC4SLEN4DLENS3spv2lo3LO04LOSPS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c242AnS3spv1X3xs02dA2dB3cnt3nXc3pXc2xs2fl2c02c83c163c242An4ZLENS3spvS3spvFFFFS3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv1X3xs02dA2dB2xs2fl2c02c83c163c242AnS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c242AnS3spv1X3xs02dA2dB3cnt3nXc3pXc2xs2fl2c02c83c163c242An4ZLENS3cnt3nXc3CNT2AnS3cnt3nXc3CNT2N1S3spv3nXc3SPR3NR1FFS3cnt3nXc3CNT2An3A47FFS3spv3cnt3N103SPRS3spv2loFS3spv2lo3cnt4LOSP2An3FloS3nXc2xs4LEN12N1S2AnS2dA2dB3cnt1v4CNTB2BVS3spv1X3xs02dA2dB2xs2fl2c02c83c163c242AnS3spv1X3xs02dA2dB3cnt3pXc2xs2fl2c02c83c163c242AnS1R3HIA2hcS3nXc3pXc3P47FFS3nXc3NR1S3spv1X3xs02dA2dB3cnt3nXc3pXc2xs2fl2c02c83c163c243NR12AnS3spv1X3xs02dA2dB3nXc3pXc2xs2fl2c02c83c163c243NR12AnS2dA2dB2d13cnt1v1f4CNTB2BV2BFFFFFFFS3cnt3nXc3CNT2N1SS1R3spv2lo4SLO24NRAm3SPRFS1R3spv2lo4SLO23NRM3SPRFS1R3spv2lo4SLO2FS1R3HIA3spv2lo2h24TOP25HTOP2S1R3HIA3spv2lo2h44TOP45HTOP4S1R3HIA1h3spv2lo3TOP1HFFFS3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S1R3HIA1h3spv2lo3cnt3nXc3CNT4LOSP2An3Flo1a2HaS2loFS3spv3SPA3SPRS3spv3SPA3SPRSS1R3HIA1h3spv2d14BUDF1f2BF3SPR2h24HFR1S1R3nXc3pXc2N12P02PC1HFFS3spvS3cnt3nXc3CNT2AnFS3spvFS3spv3cnt3nXc3CNT3N103SPR2N1S3spv2loFS1R3HIA3spv2h24TOP2FS1R3HIA3spv2h24TOP2FS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c242X03X162AnS3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv1X3xs02dA2dB2xs2fl2c02c83c163c242AnS3spv1X3xs02dA2dB3cnt3nXc3pXc2xs2fl2c02c83c163c242An4ZLENS1R3spv1X3xs02dA2dB2lo4SLO23cnt3nXc2xs2fl2c02c83c163c243CNT5NEEDR3LOS2X03ALO3SPR4LEN12An3An03AnCS1R3HIA1h3spv2dA2dB3BUD3cnt1v4CNTB2BV3SPR2h23HV1S2d12D01f2BFS1R3HIA1h3spv2lo1a2HaS2LB4C24H3LBc4C24cFS3spv1X3xs02dA2dB3pXc2xs2fl2c02c83c163c242AnFS3spv2lo3nXc3pXc4XLScFFS3cnt3nXc3CNT2N12xs4LEN1S3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv1X3xs02dA2dB2xs2fl2c02c83c163c242X03X162AnS1R3HIA1h3spv2d12D04BUDF1f2hc2BF3SPR4HFR1S3spv3cnt3nXc3CNT3SPR3NR1S1R3HIA2h2S3cntS3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv1X3xs02dA2dB3cnt3nXc3pXc2xs2fl2c02c83c163c242An4ZLENS2An3An02KZS3pXc2KP2P0FS1R3HIA1h3spv3TOPS1R2lo3LOSFS1R3HIA1h3spv2dA2dB3BUD3cnt1v2hc4CNTB2BV3SPR3HV1S1RS1R3spv2lo3LOS4LOSP4SP64FS2lo3cnt3nXc3CNT2An3FloS3nXc3NR1S3nXc3pXc2An3SEPS3cnt3nXc3CNT3N10S3nXcFFFFFFFFFFFFFFFFS1R3spv3xs02dA2dB2lo4SLO23cnt3nXc2xs2fl2c02c83c163c243CNT5NEEDR3LOS3ALO2An3AnC2N12HB5Ha_st5Hl_stFFFS3spv3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c242An2N14Fcnt3Flo4SLEN4DLENS3spv3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c242An2N14Fcnt3Flo4SLEN4DLENS3spv3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c242An2N14Fcnt3Flo4SLEN4DLENS1R3spv3xs02dA2dB2lo4SLO23cnt3nXc2xs2fl2c02c83c163c245NEEDR3LOS3ALO2An3AnC2N14Fcnt4SLEN4DLENS1R3spv1X3xs02dA2dB2xs2fl2c02c83c163c242HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2xs2fl2c02c83c163c242HB5Ha_st5Hl_stS3spv3xs02dA2dB2xs2fl2c02c83c163c242An2HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2xs2fl2c02c83c163c242X03XAL2AnS3spv1X3xs02dA2dB3cnt3pXc2xs2fl2c02c83c163c242X03XAL2AnS3spv3xs02dA2dB2xs2fl2c02c83c163c242HBS3spv3xs02dA2dB2xs2fl2c02c83c163c242HBS3spv3xs02dA2dB2xs2fl2c02c83c163c242HBS1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB3cnt2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c244ZLENS3xs02dA2dB3cnt3nXc2xs2fl2c02c83c163c242An4SLEN4DLENS1R3spv1X3xs02dA2dB2lo2xs2fl2c02c83c163c242HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2lo2xs2fl2c02c83c163c242HB5Ha_st5Hl_stS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c242An2HB5Ha_st5Hl_stS1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB3cnt2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S1R3spv3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDR3LOS4SP643ALO3ACPS1R3spv3xs02dA2dB2lo4SLO23cnt3nXc2xs2fl2c02c83c163c245NEEDR3LOS4SP643ALO3ACP4ZLENS1R3spv3xs02dA2dB2lo4SLO23cnt3nXc2xs2fl2c02c83c163c245NEEDR3LOS4SP643ALO3ACP2N14SLEN4DLENS1R3spv3xs02dA2dB2lo4SLO23cnt3nXc2xs2fl2c02c83c163c245NEEDR3LOS4SP643ALO3ACP4ZLENS1R3spv3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDR3LOS4SP643ALO3ACPS1X3xs02dA2dB3cnt2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB3cnt2xs2fl2c02c83c163c24S3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c244SLEN4DLENS1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c244ZLENS3xs02dA2dB3cnt3nXc2xs2fl2c02c83c163c242An2N14Fcnt4SLEN4DLENS3spv3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c244SLEN4DLENS1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv3xs02dA2dB2xs2fl2c02c83c163c244SP642HB5Ha_stS3spv3xs02dA2dB2xs2fl2c02c83c163c244SP642HB5Ha_stS3spv3xs02dA2dB2xs2fl2c02c83c163c244SP642HB5Ha_stS1R3spv3xs02dA2dB2lo4SLO23cnt3nXc3pXc2xs2fl2c02c83c163c245NEEDR3LOS3ALO2PC4ZLENS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS3spv3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c244LOSP4ZLENFFFFS1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB3cnt2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB3cnt2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS3spv3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c244LOSP4ZLENS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c244ZLENS3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c242X0S1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB3cnt2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS3spv3xs02dA2dB2lo3cnt3nXc2xs2fl2c02c83c163c244LOSP4ZLENS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS1R3spv1X3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSP2HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSP2HB5Ha_st5Hl_stS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSP2An2HB5Ha_st5Hl_stS1X3xs02dA2dB2xs2fl2c02c83c163c24S3xs02dA2dB2xs2fl2c02c83c163c24". (* [comment removed for export] *)
  #[using="IMG ZF CMUL CALLOC AMC AMS JC TPV D0 NXA NXB BUD BUDF SLO2 C24H KCL"] Lemma mw_GROW1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pi,$2.Pj,$2.Pcnt,$2.Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pfl,(4.&40.)Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R12.R11.R10.R?.R13.(3>.&40.(1<.(21.VdB,)+8.))(3>.&40.(21.VdA,))(3>.&40.(1<.(21.VdA,)+8.)))(35.$1.)R19.R18.R17.R16.R15.R14.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R18.R17.R16.R15.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R19.R18.R17.R16.)P,(2<.$2;.R18.(2=.VR,)(52.$2;.VR,VHIA,Vh,)(>.&40.Vspe,)(>.&40.Vspv,)Vd1,)P,(14.(19.=R20.)(19.R20.(1>.VdA,)))P,(14.(19.=R20.)(19.R20.(1>.VdB,)))P,(19.(1<.R22.R21.)R20.)P,(1;.(1>.R1;.)R21.)P,(19.R22.+2710.)P,(19.R23.(1<.(1<.(1>.VdA,)(1>.VdB,))+1.))P,(19.R23.=)P,(19.R23.=)P,(19.(1>.R20.)(39.VnX,VdA,VdB,))P,(19.R27.(39.VnX,VdA,VdB,))(3:.$2;.(3;.$2;.VR,VHIA,R25.Vmo,)VPOST,(3<.(3=.R1<.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R1;.R1:.R19.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))R18.R17.(3>.&40.(1<.(4:.(1<.VX,+:.)+3.)(4;.(47.VR,))))(3>.&40.(1<.VX,+:.))R16.R15.R14.R13.Vxs2,(3>.&40.R28.)(3>.&40.(4;.(47.VR,)))Vxs5,(3>.&40.(21.VdB,))(3>.&40.VX,)(3>.&40.-10.)Vxs9,(3>.&40.R2:.)(3>.&40.R29.)R12.R11.R10.R?.)VF,(3>.&40.+9><24.)Vfc,(3?.(4.&40.))R23.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J RA RB UW HI_ HJ HN CNT N10 CNTB BV BF SZ CSZ.
    pose proof (JC c0 c8 c16 c24 fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(bv_unsigned spv + -64, bv_unsigned spv)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (xa_fr_store _ _ _ _ _ _ _ _ _ _ _ c0 c8 SH10 (Z_to_bv 64 (X + 10)) fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))
                  _ _ _ _ m1 J MU WM MI1 ST1 HH1 FR1) as J1.
    pose proof (ride_fr_store dA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J RA MU WM) as RA1.
    pose proof (ride_fr_store dB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J RB MU WM) as RB1.
    pose proof (uwc_fr_store _ _ UW MU) as UW1.
    clear J RA RB UW MU WM.
    pose proof (JC c0 c8 SH10 (Z_to_bv 64 (X + 10)) fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))) as JC1.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 429840) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ J1) as C24c.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := cnt) (sz := 4) (lo := lo) (d := d1);
        rewrite ?(unsigned_lit (bv_unsigned spv + -64)) by qlia; try eassumption; try reflexivity.
      all: try (rewrite HS1; eapply uwc_floor; [exact UW1| clear; lia]).
      all: try (rewrite HT1; clear - TOP; lia).
      all: try (intros _; clear - C24c C24H; lia).   (* [comment removed for export] *)
      all: unfold mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
           clear - CNT CNTB N10 NR1 NR NRA NRB LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP; try lia.
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned spv + -64)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2. clear MU WM.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof ST2 as ST2'. replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) in ST2' by (clear; lia).
    assert (HP2' : presA asegs R LBc LF (bv_unsigned spv - 64) (arl_stklo R) (hstkhi asegs R HIA hc) [] m1 m2).
    { eapply presA_weaken; [exact HP2| intros bq Hb; exact Hb| intros bq Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    assert (UW2 : UWC m2).
    { rewrite <- HS1. eapply (uwc_presA_w R); [exact HP2| rewrite HS1; exact UW1| clear; lia| intros a Ha; exact I| clear - LO0 LOSP; lia| apply hstkhi_le64; clear - LOS LOSP SP64; lia]. }
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned spv <= htop asegs R HIA h2) by (rewrite HT2, HT1; exact TOP).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ _ _ _ J1 MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep.
      eapply (KCL _ _ _ _ _ _ (-16)); [exact J2| right; reflexivity| | | cbn [md_n]; exact SZ].
      + unfold mul_mid_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT CNTB NR1. lia.
      + unfold mul_mid_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      replace (cnt * 4) with (4 * cnt) in HFRA, HAS, HH2, HNEW, HV2 by (clear; lia).
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ _ _ _ An cnt J1 MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW
                  ltac:(cbn [md_n]; clear - CNT N10; lia)) as [J2 F2].
      pose proof (rideA_transport R HIA h LB LF m dX spv lo 64 _ JC1 dA _ _ _ _ _ _ _ _ _ _ J1 RA1 HP2' MI2 HCS2 HH2 ltac:(intros b' Hb; right; exact Hb)) as RA2.
      pose proof (rideA_transport R HIA h LB LF m dX spv lo 64 _ JC1 dB _ _ _ _ _ _ _ _ _ _ J1 RB1 HP2' MI2 HCS2 HH2 ltac:(intros b' Hb; right; exact Hb)) as RB2.
      dpose HFRA as (An0 & AnC & AnD & HAP).
      clear J1 RA1 RB1 UW1. try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1; try clear CX1; try clear OWN0; try clear OWN1.
      xa_open J2.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & OWN0 & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold mpi_cells in CX2.
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH1) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - An0 AnC H; lia); clear - KZ An0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases KP; zify_cond KP.
      + (* [comment removed for export] *)
        assert (EO : own = LNull).
        { destruct own; [reflexivity| | exfalso; exact (NS1 eq_refl)]. exfalso.
          ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & _ & _ & _ & P0 & PC & _).
          rewrite Z.mod_small in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H N1; lia). clear - KP P0; lia. }
        subst own. ddestruct (OWN0 eq_refl) as (EP & EN & EL). clear OWN1 KP.
        pose proof (xga_null _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2.
        eapply (mw_GFIN i j cnt); [exact D2| exact RA2| exact RB2| exact HI_| exact HJ| exact HN| | | exact CSZ].
        * unfold mul_mid_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT CNTB NR1. lia.
        * unfold mul_mid_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
      + (* [comment removed for export] *)
        assert (EO : own = LHeap).
        { destruct own; [| reflexivity| exfalso; exact (NS1 eq_refl)]. exfalso. apply KP. rewrite (proj1 (OWN0 eq_refl)). reflexivity. }
        subst own. ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47). clear OWN0 OWN1 KP.
        pose proof (XLS1 ltac:(discriminate)) as XLSc. pose proof (XP1 eq_refl) as XPc.
        (* [comment removed for export] *)
        shadow_byte OX1 (X + 10) 2 as k RD HK. zstep. clear RD. zstep.
        shadow_merge_regs2_a (X + 10) k HK 13 12.
        (* [comment removed for export] *)
        zstep.
        replace (zx16 (Z_to_bv 64 nXc)) with (Z_to_bv 64 nXc)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
        clear MU WM. pose proof (munch_refl [(bv_unsigned spv + -64, bv_unsigned spv)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        zstep.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2b end.
        pose proof (xa_fr_store _ _ _ _ _ _ _ _ _ _ _ c0 (Z_to_bv 64 An) SH10 (Z_to_bv 64 (X + 10)) fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))
                      _ _ _ _ m2b J2 MU WM MI1 ST1 HH1 FR1) as J2b.
        pose proof (ride_fr_store dA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2b J2 RA2 MU WM) as RA2b.
        pose proof (ride_fr_store dB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2b J2 RB2 MU WM) as RB2b.
        pose proof (uwc_fr_store _ _ UW2 MU) as UW2b.
        pose proof F2 as [Ffr Ffr0 Fal Fnew Fnewc Fap Farr Flen Fcnt FXS Flo]. cbn [md_n] in Fcnt.
        pose proof (fba_munch asegs R LB LF dX lo _ _ _ _ _ _ _ m2b F2 MU WM
                      ltac:(cbn [disjoint_from]; split; [clear - Flo LOSP; lia| exact I])) as F2b.
        clear Farr.
        clear J2 RA2 RB2 UW2 F2 MU WM.
        pose proof (JC c0 (Z_to_bv 64 An) SH10 (Z_to_bv 64 (X + 10)) fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))) as JC2.
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1; try clear CX2.
        xa_open J2b. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
        unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
        destruct (xga_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JC2 _ _ _ _ _ _ _ _ _ J2b F2b eq_refl)
          as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _ & OA & OP' & _ & A47 & INA & INP).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP, OA, OP', A47, INA, INP.
        rewrite firstn_length in DST, DLEN. rewrite repeat_length in DST, DLEN.
        replace (Init.Nat.min (Z.to_nat nXc) (Z.to_nat cnt)) with (Z.to_nat nXc) in DST, DLEN by (clear - CNT N1; lia).
        pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_MM) as SPC. unfold A_ASAN_MEMCPY_MM in SPC.
        apply (u8arr_of_rw_cells asegs) in DST.
        pose proof (munch_refl [(An, An + 4 * nXc); (lo, bv_unsigned spv + -64)] m2b) as MU. pose proof (wmono_refl asegs m2b) as WM.
        (* [comment removed for export] *)
        zstep.
        acallxA_sp (bv_unsigned spv + -64)
          (eapply SPC with (h := h2) (LB := (An, 4 * cnt) :: LBc) (LF := LF) (DST := An) (SRC := pXc) (n := 4 * nXc) (lo := lo)
                            (ss := u32s xs);
           rewrite ?(unsigned_lit (bv_unsigned spv + -64)) by qlia;
           try eassumption; try reflexivity;
           first [ left; rewrite AMC; reflexivity
                 | rewrite u32s_length, firstn_length, repeat_length; clear - N1 CNT; lia
                 | rewrite u32s_length; clear - LEN1 N1; lia
                 | eapply aobj_sub; [exact OA| clear; lia| clear - CNT N1; lia]
                 | right; clear - SEP; lia
                 | left; clear - Flo CNT N1 SLO2 NEEDR; lia
                 | clear - XLSc SLO2 NEEDR; lia
                 | right; clear - A47 CNT N1; lia
                 | right; clear - P47; lia
                 | eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]
                 | eapply client_wrange_block; [apply in_or_app; left; left; reflexivity| clear; lia| clear - CNT N1; lia]
                 | f_equal; clear; lia
                 | clear - NR1 N1 CNT LOS SLO SLO2 NEEDR NRAm TOP2 SPA SPR; lia
                 | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]).
        clear SPC.
        all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : u8arr asegs m3 An (u32s xs) |- _ => rename H into HPA end.
        match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
        match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
        match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
        match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 X 16 |- _ => rename H into OX3 end.
        pose proof ST3 as ST3'. replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) in ST3' by (clear; lia).
        apply (rw_cells_of_u8arr asegs) in HPA. rewrite u32s_length in HPA.
        replace (4 * length xs)%nat with (Z.to_nat (4 * nXc)) in HPA by (clear - LEN1 N1; lia).
        pose proof MU as MU3. replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) in MU3 by (clear; lia).
        destruct (xga_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JC2 _ _ _ _ _ _ _ _ _ m3 J2b F2b eq_refl MU3 WM MI3 ST3' HPA HH3 OX3) as [J3 F3].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3, F3.
        assert (WC3 : w_client (hcs asegs R HIA h2) [(An, An + 4 * nXc); (lo, bv_unsigned spv + -64)]).
        { unfold w_client; apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [eapply aobj_crange; exact OA| clear; lia| clear - CNT N1; lia]|].
          apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SLO2 NEEDR; lia]| apply Forall_nil]. }
        pose proof (rideA_fresh_munch R HIA h LB LF m dX spv lo 64 _ JC2 dA _ _ _ _ _ _ _ _ _ (4 * nXc) m3 (bv_unsigned spv + -64) J2b F2b RA2b ltac:(clear - CNT N1; lia) ltac:(clear; lia) MU WM WC3) as RA3.
        pose proof (rideA_fresh_munch R HIA h LB LF m dX spv lo 64 _ JC2 dB _ _ _ _ _ _ _ _ _ (4 * nXc) m3 (bv_unsigned spv + -64) J2b F2b RB2b ltac:(clear - CNT N1; lia) ltac:(clear; lia) MU WM WC3) as RB3.
        assert (UW3 : UWC m3).
        { eapply uwc_munch; [exact UW2b| exact MU| clear - LO0 LOSP; lia| apply hstkhi_le64; clear - LOS LOSP SP64; lia|].
          intros a Ha. cbn [outside]. split; [clear - Ha Flo LOSP CNT N1; lia| split; [clear - Ha; lia| exact I]]. }
        clear J2b F2b RA2b RB2b UW2b WC3 OA OP' SBY SLEN DLEN INA INP MU3.
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. xa_open J3. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
        unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
        pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC2 _ _ _ _ _ _ _ J3) as (_ & _ & _ & _ & CX3 & _ & _).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
        (* [comment removed for export] *)
        clear MU WM. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        zstep. zstep. zstep.
        replace (zx16 (Z_to_bv 64 nXc)) with (Z_to_bv 64 nXc)
          by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
        zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
        destruct (xga_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JC2 _ _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB & ZN1).
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ZIN, ZCH, ZLEN, ZB.
        pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
        eapply aevtA_call.
        { intros mo3 [HK3 MF3].
          eapply SPZ with (h := h2) (LB := (An, 4 * cnt) :: LBc) (LF := LF) (buf := pXc) (len := 4 * nXc) (lo := lo) (d := d1) (junk := u32s xs);
            rewrite ?(unsigned_lit (bv_unsigned spv + -64)) by qlia; try eassumption; try reflexivity.
          all: try (right; split; [exact ZIN | rewrite <- ZLEN; exact ZCH]).
          all: try (rewrite HS1; eapply uwc_floor; [exact UW3| clear; lia]).
          all: try (f_equal; clear; lia).
          all: unfold mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
               clear - CNT CNTB N10 NR1 NR NRA NRB N1 LOS SLO SLO2 NEEDR NRM NRF SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP TOP2; try lia.
          all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
        clear SPZ.
        (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
        destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
        rewrite ?(unsigned_lit (bv_unsigned spv + -64)) in PO by qlia.
        ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
          replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
        match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
        presA_transport HP4.
        pose proof ST4 as ST4'. replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) in ST4' by (clear; lia).
        assert (HP4' : presA asegs R (lb_remove pXc ((An, 4 * cnt) :: LBc)) LF (bv_unsigned spv - 64) (arl_stklo R) (hstkhi asegs R HIA h2)
                         [(pXc, pXc + 4 * nXc)] m3 m4).
        { eapply presA_weaken; [exact HP4| intros bq Hb; exact Hb| intros bq Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
        pose proof (xga_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JC2 _ _ _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 eq_refl MI4 ST4' HP4' HT4 HS4 HF4 HCS4 HV4 HFR4 HH4) as D4.
        pose proof (rideA_zfree R HIA h LB LF m dX spv lo 64 _ JC2 dA _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 RA3 eq_refl HP4' MI4 HCS4 HH4) as RA4.
        pose proof (rideA_zfree R HIA h LB LF m dX spv lo 64 _ JC2 dB _ _ _ _ _ _ _ _ _ m4 h4 J3 F3 RB3 eq_refl HP4' MI4 HCS4 HH4) as RB4.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in D4, RA4, RB4.
        apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
        clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo) as KINV.
        clear CSOK SB64 SCS0 SCS HTOP2.
        pose proof (hcs_ok asegs R HIA h4) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h4) as SCS0.
        assert (TOP4 : bv_unsigned spv <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
        assert (VF4 : v + (2 * (4 * cnt) + AVOL_CALL) + AVOL_CALL <= mul_mid_PHI dA dB /\ f + fr_charge d1 + fr_charge d1 <= mul_mid_FR d1).
        { unfold mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge in *; unfold AVOL_CALL in *. clear - BV BF CNT CNTB NR1 D0. lia. }
        try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1. clear J3 F3 RA3 RB3 UW3 HP4 HP4'. try clear ZCH; try clear ZB; try clear XARR; try clear OP; try clear HH2; try clear CX3.
        pose proof D4 as [DMI DST4 DFR DHM DHT DHS DHF DHCS DHV DHFR DCX DSG DSUB DKEEP DGONE DNEW DAPART DARR DLEN4 DCNT DXS DPRES DFRESH DAL DOX DLO DNM].
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in DCX, DOX, DHM.
        unfold mm_fr in DFR. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in DFR by (clear; lia).
        pose proof (hm_top asegs R HIA h4 _ LF m4 DHM) as HTOP4.
        assert (SCS : crange (hcs asegs R HIA h4) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP4 HTOP4; lia]).
        pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        eapply (mw_GFIN i j cnt); [exact D4| exact RA4| exact RB4| exact HI_| exact HJ| exact HN| exact (proj1 VF4)| exact (proj2 VF4)| exact CSZ].
    all: match goal with |- ?g => idtac "GROW1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@D13554616751.171D13554616751.172D2000233302.202 D2000233302.204 D40944481165.204D50818716548.171D50818716548.172K42587433812.171K42587433812.172L1000762305.4   L11147441822.1  L11385475062.1  L13642019862.167L13642019862.215L17971934183.36 L21814223730.4  L23073757250.9  L23100341967.215L23615739305.3  L33668935836.36 L35655538624.7  L35663928186.7  L37417854423.6  L37727358070.167L39039957623.36 L39436426759.7  L41707467178.1  L42594106808.2  L42602157212.1  L46225601430.166L46225601430.215L46756382136.215L4762891152.4   L47834816178.4  L48154966246.215L5259801613.214 L536504997.36   L53812879153.36 L54980800062.1  L55785555446.166L58385364829.2  L59308546384.3  L59308633593.3  L59308972243.3  L59321342598.4  L60013347957.5  L60098763854.3  L61562785068.36 L62018535662.1  L62030908141.6  L6639274391.204 L67380509172.4  Q11801279589.171Q11801279589.172Q12370813529.219Q15457446739.168Q15457446739.169Q17207432298.218Q18363828416.168Q18366170748.218Q25513505925.170Q25513505925.171Q30985055127.191Q30987329589.173Q37625261960.218Q49698585326.169Q49698585326.170Q52182444307.203Q5485126037.218 Q5485174314.219 Q58132722221.167Q58132722221.218Q59842863100.167Q59842863100.218Q6143569392.219 Q64139569937.168Q64141419949.218Q7377275490.170 Q7377275490.171 00001?02N02O02P03504C05Q06]07i08:08?08D08i09Q09b0:50:J0;20;<0;S0;o0<E0<]0=B0=O0=e0=j0=k0>00>U0?=0@U0@a0A30A40Ac0BL0Be0Bj0CO0CY0Cf0D10D<0D=0DN0DX0EH0EK0Ec0FH0FY0GO0HC0I20IX0J>0J_0KE0Kk0Ld0M[0N_0Oc0PD0Q50Qf0Qg0RH0Ri0ST0T?0Te0UK0Ul0VW0WB0X@0Y<S1R3spv1X3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stFFS3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S1R3HIA1h3spv1X3xs02dA2dB2hc2xs2fl2c02c83c163c243TOP2X03SPR3HT12HB5Ha_st5Hl_stS1R3HIA1h3spv1X3xs02dA2dB2hc2xs2fl2c02c83c163c243TOP2X03SPR3HT12HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO23pXc2xs2fl2c02c83c163c245NEEDR3DSX2HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO23pXc2xs2fl2c02c83c163c245NEEDR3DSX2HB5Ha_st5Hl_stS3spv2lo3LO04LOSPS3spvS3spvS3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv1X3xs02dA2dB2xs2fl2c02c83c163c242AnS3spv3cnt3N103SPRS3cnt3dXc4CNT04CNT1S2dA2dB3cnt1v2BV4CNTBS3spv1X3xs02dA2dB2xs2fl2c02c83c163c242AnS1R3HIA2hcS1R3spv2lo4SLO23NRM3SPRS1R3HIA3spv2lo2h24TOP25HTOP2S1R3HIA1h3spv2lo3TOP1HS2dA2dB3NRA3NRB3cnt4CNT1S3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv3SPA3SPRS1R3nXc3pXc2N12P02PC1HS3spvFS3spvS3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv1X3xs02dA2dB2xs2fl2c02c83c163c242AnS1R3spv1X3xs02dA2dB2lo4SLO23cnt2xs2fl2c02c83c163c244CNT15NEEDR3LOS2X03ALO3SPR2An3An03AnCS2d12D01f2BFS2LB4C24H3LBc4C24cFS3spv1X3xs02dA2dB2xs2fl2c02c83c163c242X03X162AnS1R3HIA1h3spv2d12D04BUDF1f2hc2BF3SPR4HFR1S3spv3cnt3nXc3CNT3SPR3NR1S3cntS3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S3cnt4CNT1S3nXc4CNT02N1S2An3An02KZS3pXc2KP2P0FS1R3HIA1h3spv3TOPS1R2lo3LOSS1R3HIA1h3spv2dA2dB3BUD3cnt1v2hc2BV4CNTB3SPR3HV1S1RS1R3spv2lo3LOS4LOSP4SP64S3spv1X3xs02dA2dB2xs2fl2c02c83c163c24S3cnt3nXc3CNT3N10S1R3spv1X3xs02dA2dB2xs2fl2c02c83c163c242HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2xs2fl2c02c83c163c242HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2xs2fl2c02c83c163c242X03XAL2AnS3spv3xs02dA2dB2xs2fl2c02c83c163c242HBS3spv3xs02dA2dB2xs2fl2c02c83c163c242HBS1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S1R3spv1X3xs02dA2dB2lo2xs2fl2c02c83c163c242HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2lo2xs2fl2c02c83c163c242HB5Ha_st5Hl_stS1R3spv3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDR3LOS4SP643ALO3ACPS1R3spv3xs02dA2dB2lo4SLO22xs2fl2c02c83c163c245NEEDR3LOS4SP643ALO3ACPS1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv3xs02dA2dB2xs2fl2c02c83c163c244SP642HB5Ha_stS3spv3xs02dA2dB2xs2fl2c02c83c163c244SP642HB5Ha_stFS1X3xs02dA2dB2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c24S1X3xs02dA2dB2xs2fl2c02c83c163c24S3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS3spv3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSPS1R3spv1X3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSP2HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2lo2xs2fl2c02c83c163c244LOSP2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG CMUL CALLOC AMS JC TPV D0 NRA NRB NXA NXB BUD BUDF SLO2 C24H KCL"] Lemma mw_GROW2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pi,$2.Pj,$2.Pcnt,$2.Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pfl,(4.&40.)Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxs3,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R13.R12.R11.R10.R14.(3>.&40.(1<.(21.VdB,)+8.))(3>.&40.(21.VdA,))(3>.&40.(1<.(21.VdA,)+8.)))(35.$1.)R1:.R19.R18.R17.R16.R15.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R19.R18.R17.R16.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R1:.R19.R18.R17.)P,(2<.$2;.R19.(2=.VR,)(52.$2;.VR,VHIA,Vh,)(>.&40.Vspe,)(>.&40.Vspv,)Vd1,)P,(14.(19.=R21.)(19.R21.(1>.VdA,)))P,(14.(19.=R21.)(19.R21.(1>.VdB,)))P,(19.(1<.R23.R22.)R21.)P,(15.$2.(1>.R1<.)=)P,(15.$2.R23.+1.)P,(19.R23.=)P,(19.R23.=)P,(19.(1>.R20.)(39.VnX,VdA,VdB,))P,(19.R27.(39.VnX,VdA,VdB,))(3:.$2;.(3;.$2;.VR,VHIA,R25.Vmo,)VPOST,(3<.(3=.R1<.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R1;.R1:.R19.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))R18.R17.(3>.&40.(1<.(4:.(1<.VX,+:.)+3.)(4;.(47.VR,))))(3>.&40.(1<.VX,+:.))R16.R15.R14.R13.Vxs2,R12.(3>.&40.(4;.(47.VR,)))Vxs5,(3>.&40.(21.VdB,))(3>.&40.VX,)(3>.&40.-10.)Vxs9,(3>.&40.R2:.)(3>.&40.R29.)R11.R10.R?.R>.)VF,(3>.&40.+9><88.)Vfc,(3?.(4.&40.))R23.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J RA RB UW HI_ HJ HN CNT0 CNT1 BV BF SZ CSZ.
    assert (CNT : md_n dXc < cnt) by (clear - CNT0 CNT1; lia). assert (N10 : cnt <= 10000) by (clear - CNT1; lia).
    assert (CNTB : cnt <= md_n dA + md_n dB + 1) by (clear - CNT1 NRA NRB; lia).
    pose proof (JC c0 c8 c16 c24 fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(bv_unsigned spv + -64, bv_unsigned spv)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (xa_fr_store _ _ _ _ _ _ _ _ _ _ _ c0 c8 SH10 (Z_to_bv 64 (X + 10)) fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))
                  _ _ _ _ m1 J MU WM MI1 ST1 HH1 FR1) as J1.
    pose proof (ride_fr_store dA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J RA MU WM) as RA1.
    pose proof (ride_fr_store dB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J RB MU WM) as RB1.
    pose proof (uwc_fr_store _ _ UW MU) as UW1.
    clear J RA RB UW MU WM.
    pose proof (JC c0 c8 SH10 (Z_to_bv 64 (X + 10)) fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))) as JC1.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 1) with (Z_to_bv 64 cnt) by (rewrite CNT1; reflexivity).
    replace (Z_to_bv 64 429840) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    pose proof (xa_cnt24 _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ J1) as C24c.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := LBc) (LF := LF) (cnt := cnt) (sz := 4) (lo := lo) (d := d1);
        rewrite ?(unsigned_lit (bv_unsigned spv + -64)) by qlia; try eassumption; try reflexivity.
      all: try (rewrite HS1; eapply uwc_floor; [exact UW1| clear; lia]).
      all: try (rewrite HT1; clear - TOP; lia).
      all: try (intros _; clear - C24c C24H; lia).   (* [comment removed for export] *)
      all: unfold mul_mid_PHI, mul_mid_FR, grow_PHI, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *;
           clear - CNT CNTB N10 NR1 NR NRA NRB LOS SLO SLO2 NEEDR NRM SPA SPR BUD BUDF BV BF HV1 HFR1 D0 LOSP; try lia.
      all: match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned spv + -64)) in PO by qlia.
    ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
    presA_transport HP2. clear MU WM.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof ST2 as ST2'. replace (bv_unsigned spv + -64) with (bv_unsigned spv - 64) in ST2' by (clear; lia).
    assert (HP2' : presA asegs R LBc LF (bv_unsigned spv - 64) (arl_stklo R) (hstkhi asegs R HIA hc) [] m1 m2).
    { eapply presA_weaken; [exact HP2| intros bq Hb; exact Hb| intros bq Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    assert (UW2 : UWC m2).
    { rewrite <- HS1. eapply (uwc_presA_w R); [exact HP2| rewrite HS1; exact UW1| clear; lia| intros a Ha; exact I| clear - LO0 LOSP; lia| apply hstkhi_le64; clear - LOS LOSP SP64; lia]. }
    clear CSOK SB64 SCS0 SCS HTOP.
    pose proof (hcs_ok asegs R HIA h2) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof (hcs_stack asegs R HIA h2) as SCS0.
    assert (TOP2 : bv_unsigned spv <= htop asegs R HIA h2) by (rewrite HT2, HT1; exact TOP).
    destruct CASES as [[Er HH2] | (An & Er & A16 & HFRA & HAS & HH2 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (xa_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ _ _ _ J1 MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep.
      eapply (KCL _ _ _ _ _ _ (-16)); [exact J2| right; reflexivity| | | cbn [md_n]; exact SZ].
      + unfold mul_mid_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT CNTB NR1. lia.
      + unfold mul_mid_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
    - (* [comment removed for export] *)
      replace (cnt * 4) with (4 * cnt) in HFRA, HAS, HH2, HNEW, HV2 by (clear; lia).
      destruct (xa_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ _ _ _ An cnt J1 MI2 ST2' HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 A16 HFRA HNEW
                  ltac:(cbn [md_n]; clear - CNT N10; lia)) as [J2 F2].
      pose proof (rideA_transport R HIA h LB LF m dX spv lo 64 _ JC1 dA _ _ _ _ _ _ _ _ _ _ J1 RA1 HP2' MI2 HCS2 HH2 ltac:(intros b' Hb; right; exact Hb)) as RA2.
      pose proof (rideA_transport R HIA h LB LF m dX spv lo 64 _ JC1 dB _ _ _ _ _ _ _ _ _ _ J1 RB1 HP2' MI2 HCS2 HH2 ltac:(intros b' Hb; right; exact Hb)) as RB2.
      dpose HFRA as (An0 & AnC & AnD & HAP).
      clear J1 RA1 RB1 UW1. try clear MI1; try clear ST1; try clear FR1; try clear HH1; try clear HT1; try clear HS1; try clear HF1; try clear HCS1; try clear HV1; try clear HFR1; try clear MX1; try clear AD1; try clear PD1; try clear NS1; try clear OUT1; try clear FRS1; try clear FRA1; try clear HPX1; try clear OX1; try clear XP1; try clear XLS1; try clear NM1; try clear CX1; try clear OWN0; try clear OWN1.
      xa_open J2.
      pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ J2) as (_ & _ & _ & _ & CX2 & OWN0 & OWN1).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold mpi_cells in CX2.
      pose proof (hm_top asegs R HIA h2 _ LF m2 HH1) as HTOP2.
      assert (SCS : crange (hcs asegs R HIA h2) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
      unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - An0 AnC H; lia); clear - KZ An0; lia|]. clear KZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 1) with (Z_to_bv 64 cnt) by (rewrite CNT1; reflexivity).
      (* [comment removed for export] *)
      zstep. if_cases KP; zify_cond KP.
      + (* [comment removed for export] *)
        assert (EO : own = LNull).
        { destruct own; [reflexivity| | exfalso; exact (NS1 eq_refl)]. exfalso.
          ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & _ & _ & _ & P0 & PC & _).
          rewrite Z.mod_small in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H N1; lia). clear - KP P0; lia. }
        subst own. ddestruct (OWN0 eq_refl) as (EP & EN & EL). clear OWN1 KP.
        pose proof (xga_null _ _ _ _ _ _ _ _ _ _ _ _ JC1 _ _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2.
        eapply (mw_GFIN i j cnt); [exact D2| exact RA2| exact RB2| exact HI_| exact HJ| exact HN| | | exact CSZ].
        * unfold mul_mid_PHI, grow_PHI in *; unfold AVOL_CALL in *. clear - BV CNT CNTB NR1. lia.
        * unfold mul_mid_FR, calls_FR, fr_charge in *. clear - BF D0. lia.
      + (* [comment removed for export] *)
        exfalso. destruct own; [apply KP; rewrite (proj1 (OWN0 eq_refl)); reflexivity| | exact (NS1 eq_refl)].
        ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & _). clear - N1 CNT0. lia.
    all: match goal with |- ?g => idtac "GROW2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@D13554616751.165D50818716548.165K42587433812.165L11385475062.1  L19843951665.4  L24873264023.163L2749810431.3   L32436885838.4  L32967940548.6  L33323889460.2  L34911638000.3  L35663928186.7  L36618624197.2  L39733091698.4  L42594106808.2  L43753364214.160L44894671497.159L46160487540.163L46160821889.160L49539960738.7  L49786828438.160L52274802212.2  L56971279505.6  L60098763854.3  L62650482766.5  L65448092613.2  L65450274296.164L65450274431.163Q11801279589.165Q1449727789.161 Q15457446739.162Q25513505925.164Q26207421841.164Q26207721832.165Q26207967338.162Q31654082872.164Q39212284437.165Q43925228937.165Q44648629500.161Q49698585326.163Q60511567613.165Q60697995187.165Q7377275490.164 Q8880503606.162 Q9538787269.162 00001D02W03d03i04505105905E05W05\05f06<06E06Q06R07908:08h09V09k0:R0:W0:k0;50;D0;M0<80<c0=Z0>G0>o0?i0@L0@o0AR0B50BX0C;0Cc0DV0E70E]0F\0G?0G`S1R3spv1X3xs02dA2dB2lo4SLO23dXc2fl2c02c83c163c243c325NEEDR3LOS2X03SPR2HB5Ha_st5Hl_stS1R3HIA1h3spv1X3xs02dA2dB2hc3dXc2fl2c02c83c163c243c323TOP2X03SPR3HT12HB5Ha_st5Hl_stS1R3spv1X3xs02dA2dB2lo4SLO23dXc2fl2c02c83c163c243c325NEEDR3DSX2HB5Ha_st5Hl_stS3spvS2d12D01f2BFS3spv1X3xs02dA2dB1i1j3dXc2c02c83c163c243c323HI_2HJ2X03SPR2KMS1i1j2KMS1i1j3dXc2KGS2dA2dB1i1j3HI_2HJS1i1jS2nX2dA2dBS1R3HIA1h3spv2lo3TOP1HS3dXc3NR1S1i1j3dXc2KGFS3spv1X3xs02dA2dB3dXc2c02c83c163c243c32S3spv1X3xs02dA2dB3NRA3NRB1i1j3dXc2c02c83c163c243c323HI_2HJ2X03SPRS3spv1X3xs02dA2dB3dXc2c02c83c163c243c322X03X16S3spv1X3xs02dA2dB3dXc2c02c83c163c243c322X03X16S2nX2dA2dB1i1j3HI_2HJS3spv1X3xs02dA2dB3dXc2c02c83c163c243c32S1i1jS2dA2dB3NRA3NRB1v2BVS1R2lo3LOSS1i1j3dXc2KG2KNS3dXc3NR1S3spv1X3xs02dA2dB3dXc2c02c83c163c243c323NR1S3spv1X3xs02dA2dB3dXc2c02c83c163c243c323NR1S3spv3xs02dA2dB3dXc2fl2c02c83c163c243c322HB5Ha_st5Hl_stS3spv3xs02dA2dB2lo3dXc2c02c83c163c243c324LOSPS3spv3xs02dA2dB3dXc2c02c83c163c243c322HBS3spv3xs02dA2dB2lo3dXc2fl2c02c83c163c243c322HB5Ha_st5Hl_stS1X3xs02dA2dB3dXc2c02c83c163c243c32S1X3xs02dA2dB3dXc2c02c83c163c243c32S1X3xs02dA2dB3dXc2c02c83c163c243c32S1X3xs02dA2dB3dXc2c02c83c163c243c32S1X3xs02dA2dB3dXc2c02c83c163c243c32S1X3xs02dA2dB3dXc2c02c83c163c243c32S3spv3xs02dA2dB2lo3dXc2c02c83c163c243c32S3spv3xs02dA2dB3dXc2c02c83c163c243c324SP642HB5Ha_stS3xs02dA2dB3dXc2c02c83c163c243c32S1X3xs02dA2dB3dXc2c02c83c163c243c322X0S3spv3xs02dA2dB2lo3dXc2fl2c02c83c163c243c324LOSP2HB5Ha_st5Hl_stS1X3xs02dA2dB3dXc2c02c83c163c243c32S3xs02dA2dB3dXc2c02c83c163c243c32". (* [comment removed for export] *)
  #[using="IMG ZF CMUL CALLOC AMC AMS JC TPV D0 NRA NRB NXA NXB BUD BUDF SLO2 C24H KCL"] Lemma mw_SUM : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pi,$2.Pj,$2.Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pfl,(4.&40.)Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa0,(4.&40.)Pxa2,(4.&40.)Pxa3,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxs3,(4.&40.)Pxs8,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R16.R15.R14.R13.R12.(3>.&40.(1<.(21.VdB,)+8.))(3>.&40.(21.VdA,))(3>.&40.(1<.(21.VdA,)+8.)))(35.$1.)R1=.R1<.R1;.R1:.R19.R18.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R1<.R1;.R1:.R19.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R1=.R1<.R1;.R1:.)P,(2<.$2;.R1<.(2=.VR,)(52.$2;.VR,VHIA,Vh,)(>.&40.Vspe,)(>.&40.Vspv,)Vd1,)P,(14.(19.=R23.)(19.R23.(1>.VdA,)))P,(14.(19.=R23.)(19.R23.(1>.VdB,)))P,(19.R23.=)P,(19.R23.=)P,(19.(1>.R20.)(39.VnX,VdA,VdB,))(3:.$2;.(3;.$2;.VR,VHIA,R24.Vmo,)VPOST,(3<.(3=.R1:.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R19.R18.R17.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))R16.R20.R15.R14.R13.R12.R11.R10.Vxs2,R?.(3>.&40.(4;.(47.VR,)))Vxs5,(3>.&40.(21.VdB,))(3>.&40.VX,)R>.Vxs9,(3>.&40.R28.)(3>.&40.R27.)R=.R<.R;.R:.)VF,(3>.&40.+9>;?0.)Vfc,(3?.(4.&40.))R22.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J RA RB UW HI_ HJ BV BF SZ.
    pose proof (JC c0 c8 c16 c24 c32 (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JCc _ _ _ _ _ _ _ J) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    xa_open J. unfold mpi_cells in CX1. cbn [md_addr] in CX1, OX1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(bv_unsigned spv + -64, bv_unsigned spv)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by (clear - HI_ HJ NRA NRB; lia).
    { (* [comment removed for export] *)
      eapply (KCL _ _ _ _ _ _ (-16)); [exact J| right; reflexivity| | | exact SZ].
      - unfold mul_mid_PHI, grow_PHI; unfold AVOL_CALL. clear - BV NRA NRB. lia.
      - unfold mul_mid_FR, calls_FR, fr_charge. clear - BF D0. lia. }
    replace (Z_to_bv 64 (j + i)) with (Z_to_bv 64 (i + j)) by (f_equal; clear; lia).
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (xa_fr_store _ _ _ _ _ _ _ _ _ _ _ c0 c8 c16 c24 fl (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))
                  _ _ _ _ m1 J MU WM MI1 ST1 HH1 FR1) as J1.
    pose proof (ride_fr_store dA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J RA MU WM) as RA1.
    pose proof (ride_fr_store dB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J RB MU WM) as RB1.
    pose proof (uwc_fr_store _ _ UW MU) as UW1.
    clear J RA RB UW MU WM.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX1 (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 (md_n dXc))) with (Z_to_bv 64 (md_n dXc))
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR1; lia); rewrite Z.mod_small by (clear - NR1; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases KG; zify_cond KG; rewrite ?unsigned_lit in KG by (clear - HI_ HJ NRA NRB NR1; lia).
    - (* [comment removed for export] *)
      zstep. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by (clear - NR1; lia).
      + (* [comment removed for export] *)
        assert (EO : md_own dXc = LHeap).
        { destruct (md_own dXc) eqn:EOX; [exfalso; ddestruct (OWN0 eq_refl) as (_ & EN & _); exact (KN EN)| reflexivity| exfalso; exact (NS1 eq_refl)]. }
        eapply (mw_LSET i j _ _ _ _ _ dXc); [exact J1| exact RA1| exact RB1| exact EO| exact HI_| exact HJ| clear - KG; lia| | | exact SZ].
        * unfold mul_mid_PHI, grow_PHI; unfold AVOL_CALL. clear - BV NRA NRB. lia.
        * unfold mul_mid_FR, calls_FR, fr_charge. clear - BF D0. lia.
      + (* [comment removed for export] *)
        eapply (mw_GROW2 i j 1); [exact J1| exact RA1| exact RB1| exact UW1| exact HI_| exact HJ| clear - KG KN; lia| exact KN| reflexivity| exact BV| exact BF| exact SZ| unfold mul_mid_SZ; clear; lia].
    - (* [comment removed for export] *)
      eapply (mw_GROW1 i j (i + j)); [exact J1| exact RA1| exact RB1| exact UW1| exact HI_| exact HJ| clear; lia| clear - KG; lia| clear - KM; lia| clear - HI_ HJ; lia| exact BV| exact BF| exact SZ| unfold mul_mid_SZ; clear - HI_ HJ; lia].
    all: match goal with |- ?g => idtac "SUM-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308666361.300000:S2dE2N12EZ". (* [comment removed for export] *)
  #[using="Type"] Lemma rider_scan : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "PdE,$6.Pv,$2.Pf,$2.Pfr,(0.$31.)Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.R5.(35.$1.)R7.R6.R4.R3.R2.R1.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,R9.R5.R4.R3.R2.)P,(11.(15.$2.(21.R:.)VX,))P,(19.+1.(1>.R;.))(14.(4<.$2;.R6.(1:.R<.)(4=.(25.R<.)))(14.(15.$2.(4>.(24.(4.&40.)(25.R<.)))(1>.R<.))(14.(1;.=(1:.R<.))(46.$2;.(47.VR,)(48.$2;.VR,VHIA,R8.)R6.(1:.R<.)(1=.+4.(1>.R<.))))))")
(* [comment removed for export] *).
  Proof.
    intros dE v f fr hc LBc mc dXc J [E|[DBJ B]] NE N1; [exfalso; exact (NE E)|].
    pose proof (opnd_viewA _ _ _ _ _ _ _ (bj_at _ _ _ _ _ _ _ _ _ _ B)) as [(_ & _ & _ & LENE & _ & OW) _].
    assert (EN : md_own dE <> LNull) by (intros C; rewrite C in OW; destruct OW as [_ EZ]; clear - EZ N1; lia).
    pose proof (bj_aobjL _ _ _ _ _ _ _ _ _ _ B EN) as OEL.
    split; [| split; [exact LENE| split; [| exact OEL]]].
    - destruct (md_own dE); [exfalso; exact (EN eq_refl)| ddestruct OW as (_ & _ & _ & [HB _]); exact HB| ddestruct OW as (_ & _ & _ & HB & _); exact HB].
    - destruct (md_own dE) eqn:EOE; [exfalso; exact (EN eq_refl)| | ddestruct OW as (_ & _ & P0 & _); exact P0].
      ddestruct OW as (_ & EIN & _). pose proof (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HH1. cbn [app] in HH1.
      destruct (hm_apart asegs R HIA hc LBc LF mc HH1) as [HBR _]. rewrite Forall_forall in HBR.
      destruct (HBR _ ltac:(apply in_app_iff; left; exact EIN)) as (R0 & _). cbn [fst snd] in R0. exact R0.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L12806154935.4  L12806161768.4  L21041645149.3  L23970764156.141L3118142471.2   L32584089863.3  L48367540261.4  L48367597562.3  L48827096264.2  L52514160176.141L54425651213.3  L59308583409.4  L59310648043.5  L64930767917.4  L8929159528.138 L8929620893.135 Q18402213789.139Q18402295455.136Q18402376468.141Q26295627581.139Q28760468501.136Q32303523866.139Q326359207.141  Q41280089850.139Q50458135125.139Q8943555749.136 00000<00=00E01E01M01V01W01X01^02H02Q02]02o03;04;05;05b06I07007T08;08f09M0:40:X0;<S2dB1r2HR2K2FS1k1r2HkS3spv1X3xs02dA2dB1k1r2c02c83c163c243c322Hk4LENZ3EP02HR2X03SPR2EBS2dB3NRBS2dB1r2HRFFS2dB1rS3spv1X3xs02dA2dB1k1r2c02c83c163c243c322HkS2dB1r2HRS2dB1r2Hk2HRS2dB1r4LENZ2HR3NTHS2dB1r2HR2K2S3spv1X3xs02dA2dB1k1r2c02c83c163c243c322Hk4LENZ3EP02HR2X03SPR2EBS3spv1X3xs02dA2dB1k1r2c02c83c163c243c322Hk4LENZ3EP02HR2X03SPR2EBS3xs02dA2dB1k1r2c02c83c163c243c322Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c322Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c322Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c322HkS3xs02dA2dB1k1r2c02c83c163c243c322Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c322Hk3EP02HRS3xs02dA2dB1k1r2c02c83c163c243c322Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c322Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c322HkS3xs02dA2dB1k1r2c02c83c163c243c322Hk". (* [comment removed for export] *)
  #[using="IMG ZF CMUL CALLOC AMC AMS JC TPV D0 NRA NRB NXA NXB BUD BUDF SLO2 C24H KCL"] Lemma mw_BLOOP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pk,$23.Pi,$2.Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pr,$2.Pr1,(4.&40.)Pfa,(4.&40.)Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa3,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxs3,(4.&40.)Pxs8,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(19.R17.(4>.R1?.))P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R15.R14.R13.R12.R11.(3>.&40.(1<.(21.VdB,)+8.))(3>.&40.(21.VdA,))(3>.&40.(1<.(21.VdA,)+8.)))(35.$1.)R1>.R1=.R1<.R1;.R1:.R19.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R1=.R1<.R1;.R1:.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R1>.R1=.R1<.R1;.)P,(2<.$2;.R1=.(2=.VR,)(52.$2;.VR,VHIA,Vh,)(>.&40.Vspe,)(>.&40.Vspv,)Vd1,)P,(14.(19.=R23.)(19.R23.(1>.VdA,)))P,(4<.$2;.R1?.(1:.VdB,)(4=.(25.VdB,)))P,(15.$2.(4>.(24.(4.&40.)(25.VdB,)))(1>.VdB,))P,(1;.=(1:.VdB,))P,(46.$2;.(47.VR,)(48.$2;.VR,VHIA,R24.)R22.(1:.VdB,)(1=.+4.(1>.VdB,)))P,(14.(19.+1.R21.)(19.R21.(1>.VdB,)))P,(19.R28.=)P,(19.R28.=)P,(19.(1>.R25.)(39.VnX,VdA,VdB,))P,(15.(4.&40.)R24.(3>.&40.R25.))(3:.$2;.(3;.$2;.VR,VHIA,R2:.Vmo,)VPOST,(3<.(3=.R1>.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R1=.R1<.R1;.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))(3>.&40.(1<.(1:.VdB,)(1=.+4.(=.R26.+1.))))(3>.&40.(1<.(1:.VdB,)(1=.+4.(=.R26.+1.))))R24.R1:.R19.R18.R17.R16.Vxs2,R15.(3>.&40.(4;.(47.VR,)))Vxs5,(3>.&40.(21.VdB,))(3>.&40.VX,)R14.Vxs9,(3>.&40.R2=.)R25.R13.R12.R11.R10.)VF,(3>.&40.+9>;:4.)Vfc,(3?.(4.&40.))R28.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hk J0 RA RB UW HI_ EBY LENZ EP0 OEL HR BV BF SZ ->; [exfalso; clear - Hk HR; lia|].
    pose proof (JC c0 c8 c16 c24 c32 (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MI1.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OEL (md_p dB + 4 * (r - 1)) 4.
    (* [comment removed for export] *)
    destruct (nth_error (md_limbs dB) (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR; lia].
    pose proof (u32ro_read asegs mc (md_p dB) (md_limbs dB) (r - 1) w _ EBY NTH ltac:(clear - HR; lia) eq_refl) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep.
      eapply (mw_SUM i r); [exact J0| exact RA| exact RB| exact UW| exact HI_| clear - HR; lia| exact BV| exact BF| exact SZ].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - HR NRB; lia).
      + replace (Z_to_bv 64 (md_p dB + 4 * (r - 1) + -4)) with (Z_to_bv 64 (md_p dB + 4 * (r - 1 - 1))) by (f_equal; clear; lia).
        eapply (IH i _ _ _ _ _ _ (r - 1)); try eassumption; first [clear - Hk; lia| clear - HR K2; lia| (f_equal; clear; lia)| reflexivity].
      + (* [comment removed for export] *)
        zstep. zstep. zstep.
        replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K2 HR; lia).
        eapply (mw_SUM i 0); [exact J0| exact RA| exact RB| exact UW| exact HI_| clear - NRB; lia| exact BV| exact BF| exact SZ].
    all: match goal with |- ?g => idtac "BLOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00^0@D13554616751.162D50818716548.162L11141041142.158L11385475062.1  L20624505799.3  L3118142471.2   L35663928186.7  L39172636981.0  L40853807680.3  L48825353400.1  L51601712534.158L53897494646.3  L58177949655.164L58640675965.155L58641002120.158L58936793720.2  L60098763854.3  L63432093722.2  L66988715924.163L66988729626.2  L66990877462.157L68211501598.2  P68206801384.163Q11801279589.162Q15457446739.160Q1949051331.165 Q20454051255.160Q21747999280.165Q21750569356.166Q25513505925.162Q31577733036.157Q34054137302.159Q36646300200.166Q39212284437.160Q42658418930.157Q42658435568.160Q42658925833.159Q49433500843.166Q49698585326.161Q51236054023.159Q53115228353.165Q60511567613.160Q64808918952.159Q65203304693.160Q7377275490.162 Q9538787269.157 00001D02W03>03C03K03S03i03j04204604]04h05O06=06k07207<07D08608>08i08j08k09_0:G0:h0;L0;m0<N0=E0=f0>S0?40?U0@60@W0A80Ai0B\0CD0Ce0DF0Dg0EH0FD0FeS1R3spv1X3xs02dA2dB2lo4SLO22c02c83c163c243c323c485NEEDR3LOS2X03SPR2B02HB5Ha_st5Hl_stS1R3HIA1h3spv1X3xs02dA2dB2hc2c02c83c163c243c323c483TOP2X03SPR2B03HT12HB5Ha_st5Hl_stS3spv1X3xs02dA2dB2c02c83c163c243c323c48S3spvS2dB3NB1S2dB3NRBS1R3HIA1h3spv2lo3TOP1HSS2dB3NB1S2dBS3spv1X3xs02dA2dB2c02c83c163c243c323c48S2dB3NRB2KNS3spv1X3xs02dA2dB2c02c83c163c243c323c48S3spv1X3xs02dA2dB2c02c83c163c243c323c482B03B16S3spv1X3xs02dA2dB2c02c83c163c243c323c482B03B16S2dB2KNS1R2lo3LOSS2dB3NRBS3spv1X3xs02dA2dB2c02c83c163c243c323c482B03B163NRBS2dB3NRBS3spv1X3xs02dA2dB3NRB2c02c83c163c243c323c48FFS3spv3xs02dA2dB2c02c83c163c243c323c482HB5Ha_st5Hl_stS3spv3xs02dA2dB2c02c83c163c243c323c482HBS3xs02dA2dB2c02c83c163c243c323c48S3xs02dA2dB2c02c83c163c243c323c482B0S3xs02dA2dB2c02c83c163c243c323c48S3xs02dA2dB2c02c83c163c243c323c48S3spv3xs02dA2dB2lo2c02c83c163c243c323c482HB5Ha_st5Hl_stS3xs02dA2dB2c02c83c163c243c323c48S3spv3xs02dA2dB2lo2c02c83c163c243c323c484LOSPS3xs02dA2dB2c02c83c163c243c323c48S3xs02dA2dB2c02c83c163c243c323c48S3xs02dA2dB2c02c83c163c243c323c48S3xs02dA2dB2c02c83c163c243c323c48S3xs02dA2dB2c02c83c163c243c323c48S3spv1X3xs02dA2dB2c02c83c163c243c323c482X02B03BALS3spv3xs02dA2dB2c02c83c163c243c323c484SP642HB5Ha_stS3spv3xs02dA2dB2lo2c02c83c163c243c323c48S3xs02dA2dB2c02c83c163c243c323c48S3xs02dA2dB2c02c83c163c243c323c48S3xs02dA2dB2c02c83c163c243c323c48S3xs02dA2dB2c02c83c163c243c323c48S3spv3xs02dA2dB2lo2c02c83c163c243c323c484LOSP2HB5Ha_st5Hl_stS3xs02dA2dB2c02c83c163c243c323c48". (* [comment removed for export] *)
  #[using="IMG ZF CMUL CALLOC AMC AMS JC TPV D0 NRA NRB NXA NXB BUD BUDF SLO2 C24H KCL"] Lemma mw_BENTRY : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pi,$2.Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pfa,(4.&40.)Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pc48,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa1,(4.&40.)Pxa3,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxs3,(4.&40.)Pxs11,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R16.R15.R14.R13.R12.(3>.&40.(1<.(21.VdB,)+8.))R11.(3>.&40.(1<.(21.VdA,)+8.)))(35.$1.)R1=.R1<.R1;.R1:.R19.R18.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R1<.R1;.R1:.R19.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R1=.R1<.R1;.R1:.)P,(2<.$2;.R1<.(2=.VR,)(52.$2;.VR,VHIA,Vh,)(>.&40.Vspe,)(>.&40.Vspv,)Vd1,)P,(14.(19.=R22.)(19.R22.(1>.VdA,)))P,(19.R22.=)P,(19.R22.=)P,(19.(1>.R1?.)(39.VnX,VdA,VdB,))(3:.$2;.(3;.$2;.VR,VHIA,R23.Vmo,)VPOST,(3<.(3=.R18.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R17.R16.R15.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))(3>.&40.(1<.(21.VdB,)+:.))R14.R1?.R13.R12.R11.R10.R?.Vxs2,R>.(3>.&40.(4;.(47.VR,)))Vxs5,(3>.&40.(21.VdB,))(3>.&40.VX,)(3>.&40.(21.VdA,))Vxs9,(3>.&40.R26.)R=.R<.R;.R:.R9.)VF,(3>.&40.+9>;64.)Vfc,(3?.(4.&40.))R21.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J RA RB UW HI_ BV BF SZ.
    pose proof (JC c0 c8 c16 c24 c32 (Z_to_bv 64 (md_addr dB + 8)) c48 (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    destruct (rider_view _ _ _ _ _ _ _ _ J RB NXB) as (CEB & OEB & SGB & B0 & B16 & BAL).
    xa_open J.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(bv_unsigned spv + -64, bv_unsigned spv)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OEB (md_addr dB + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 (md_n dB))) with (Z_to_bv 64 (md_n dB))
      by (unfold zx16; rewrite !unsigned_lit by (clear - NRB; lia); rewrite Z.mod_small by (clear - NRB; lia); reflexivity).
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (xa_fr_store _ _ _ _ _ _ _ _ _ _ _ c0 c8 c16 c24 c32 (Z_to_bv 64 (md_addr dB + 8)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dA + 8))
                  _ _ _ _ m1 J MU WM MI1 ST1 HH1 FR1) as J1.
    pose proof (ride_fr_store dA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J RA MU WM) as RA1.
    pose proof (ride_fr_store dB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J RB MU WM) as RB1.
    pose proof (uwc_fr_store _ _ UW MU) as UW1.
    clear J RA RB UW MU WM OEB. try clear CEB.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KN; zify_cond KN; rewrite ?Z.mod_small in KN by (clear - NRB; lia).
    { (* [comment removed for export] *)
      zstep. zstep.
      replace (Z_to_bv 64 (md_n dB)) with (Z_to_bv 64 0) by (f_equal; clear - KN; lia).
      eapply (mw_SUM i 0); [exact J1| exact RA1| exact RB1| exact UW1| exact HI_| clear - NRB; lia| exact BV| exact BF| exact SZ]. }
    assert (NB1 : 1 <= md_n dB) by (clear - KN NRB; lia). clear KN.
    destruct (rider_view _ _ _ _ _ _ _ _ J1 RB1 NXB) as (CEB & OEB & _).
    destruct (rider_scan _ _ _ _ _ _ _ _ J1 RB1 NXB NB1) as (EBY & LENB & EP0 & OEL).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    zstep. zstep. zstep.
    replace (Z_to_bv 64 (md_p dB + md_n dB * 4 + -4)) with (Z_to_bv 64 (md_p dB + 4 * (md_n dB - 1))) by (f_equal; clear; lia).
    eapply (mw_BLOOP (Z.to_nat (md_n dB)) i) with (r := md_n dB);
      first [ exact J1 | exact RA1 | exact RB1 | exact UW1 | exact HI_ | exact EBY | exact LENB | exact EP0 | exact OEL | exact BV | exact BF | exact SZ | reflexivity
            | clear - NB1 NRB; lia
            | match goal with |- ?g => idtac "BENTRY-SIDE-LEFT:" g end ].
    all: match goal with |- ?g => idtac "BENTRY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L21041645149.3  L21774718167.2  L23120643753.4  L23120701814.4  L23970764156.138L35164013511.2  L42787892550.3  L48367540261.4  L48367597562.3  L54425651213.3  L59308583409.4  L59310648043.5  L64930767917.4  L8929159528.135 L8929620893.132 Q26295627581.136Q34291222827.133Q34291305632.138Q34291402793.136Q42131479398.138Q48338484555.136Q49424719380.133Q50458135125.136Q53360483131.136Q8943555749.133 00000800>00?00K01O01W01`01a01b01k02702I02U03Y04]05E06006[07F08108`09K0:30:^0;FS1k1r2HkS2dA1rFS2dA1r2HR2K2S3spv1X3xs02dA2dB1k1r2c02c83c163c243c323c482Hk4LENZ3EP02HR2X03SPR2EBS2dA3NRAS2dA1r2HRFFS2dA1r2HRS2dA1r2Hk2HRS2dA1r4LENZ2HR3NTHS2dA1r2HR2K2S3spv1X3xs02dA2dB1k1r2c02c83c163c243c323c482Hk4LENZ3EP02HR2X03SPR2EBS3spv1X3xs02dA2dB1k1r2c02c83c163c243c323c482Hk4LENZ3EP02HR2X03SPR2EBS3xs02dA2dB1k1r2c02c83c163c243c323c482HkS3xs02dA2dB1k1r2c02c83c163c243c323c482Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c323c482Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c323c482Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c323c482Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c323c482Hk3EP02HRS3xs02dA2dB1k1r2c02c83c163c243c323c482Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c323c482HkS3xs02dA2dB1k1r2c02c83c163c243c323c482Hk2HRS3xs02dA2dB1k1r2c02c83c163c243c323c482Hk". (* [comment removed for export] *)
  #[using="IMG ZF CMUL CALLOC AMC AMS JC TPV D0 NRA NRB NXA NXB BUD BUDF SLO2 C24H KCL"] Lemma mw_ALOOP : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pk,$23.Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pr,$2.Pr1,(4.&40.)Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pc48,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxs3,(4.&40.)Pxs11,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(19.R16.(4>.R1=.))P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R15.R14.R13.R12.R11.(3>.&40.(1<.(21.VdB,)+8.))R10.(3>.&40.(1<.(21.VdA,)+8.)))(35.$1.)R1=.R1<.R1;.R1:.R19.R18.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R1<.R1;.R1:.R19.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R1=.R1<.R1;.R1:.)P,(2<.$2;.R1<.(2=.VR,)(52.$2;.VR,VHIA,Vh,)(>.&40.Vspe,)(>.&40.Vspv,)Vd1,)P,(4<.$2;.R1=.(1:.VdA,)(4=.(25.VdA,)))P,(15.$2.(4>.(24.(4.&40.)(25.VdA,)))(1>.VdA,))P,(1;.=(1:.VdA,))P,(46.$2;.(47.VR,)(48.$2;.VR,VHIA,R22.)R20.(1:.VdA,)(1=.+4.(1>.VdA,)))P,(14.(19.+1.R1?.)(19.R1?.(1>.VdA,)))P,(19.R26.=)P,(19.R26.=)P,(19.(1>.R23.)(39.VnX,VdA,VdB,))P,(15.(4.&40.)R22.(3>.&40.R23.))(3:.$2;.(3;.$2;.VR,VHIA,R28.Vmo,)VPOST,(3<.(3=.R1<.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R1;.R1:.R19.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))(3>.&40.(1<.(21.VdB,)+:.))(3>.&40.(1<.(1:.VdA,)(1=.+4.(=.R24.+1.))))(3>.&40.+1.)(3>.&40.(1<.(1:.VdA,)(1=.+4.(=.R24.+1.))))R18.R17.R16.R15.Vxs2,R14.(3>.&40.(4;.(47.VR,)))Vxs5,(3>.&40.(21.VdB,))(3>.&40.VX,)(3>.&40.(21.VdA,))Vxs9,R23.R13.R12.R11.R10.R?.)VF,(3>.&40.+9>;08.)Vfc,(3?.(4.&40.))R26.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hk J0 RA RB UW EBY LENZ EP0 OEL HR BV BF SZ ->; [exfalso; clear - Hk HR; lia|].
    pose proof (JC c0 c8 c16 c24 c32 (Z_to_bv 64 (md_addr dB + 8)) c48 (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    pose proof (xa_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MI1.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OEL (md_p dA + 4 * (r - 1)) 4.
    (* [comment removed for export] *)
    destruct (nth_error (md_limbs dA) (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR; lia].
    pose proof (u32ro_read asegs mc (md_p dA) (md_limbs dA) (r - 1) w _ EBY NTH ltac:(clear - HR; lia) eq_refl) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep.
      eapply (mw_BENTRY r); [exact J0| exact RA| exact RB| exact UW| clear - HR; lia| exact BV| exact BF| exact SZ].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - HR NRA; lia).
      + replace (Z_to_bv 64 (md_p dA + 4 * (r - 1) + -4)) with (Z_to_bv 64 (md_p dA + 4 * (r - 1 - 1))) by (f_equal; clear; lia).
        eapply (IH _ _ _ _ _ _ (r - 1)); try eassumption; first [clear - Hk; lia| clear - HR K2; lia| (f_equal; clear; lia)| reflexivity].
      + (* [comment removed for export] *)
        zstep.
        replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K2 HR; lia).
        eapply (mw_BENTRY 0); [exact J0| exact RA| exact RB| exact UW| clear - NRA; lia| exact BV| exact BF| exact SZ].
    all: match goal with |- ?g => idtac "ALOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00^0@D13554616751.160D50818716548.160L11385475062.1  L14550820926.2  L15466341142.156L21772258342.1  L23459140778.161L23459159589.2  L23461302312.155L27017364261.2  L29532535949.3  L35164013511.2  L35663928186.7  L39172636981.0  L51284464315.162L5130124662.156 L55563306247.3  L58640675965.153L58641002120.156L60098763854.3  L62562505368.3  L63104194423.2  P14554379081.161Q10042269183.163Q11801279589.160Q15457446739.158Q18135196125.157Q18135743526.155Q18136087844.158Q25513505925.160Q28027603798.157Q32655242887.157Q34224482651.155Q34421655807.157Q39212284437.158Q49698585326.159Q58692335428.158Q60511567613.158Q61264001456.164Q61265740300.163Q64768105610.158Q66375044744.164Q67327367611.163Q7377275490.160 Q8222473558.164 Q9538787269.155 00001H02_02d02e03M03Q04D04L05805@05K05S05i05j06R07:07B08108`08j09209909:09\0:T0;=0;_0<A0<c0=^0>L0?50?W0@90@[0AO0B40BV0C80CZ0D<0D^0E@0F@0G20GTS1R3spv1X3xs02dA2dB2lo4SLO22c02c83c163c243c323c403c485NEEDR3LOS2X03SPR2A02HB5Ha_st5Hl_stS1R3HIA1h3spv1X3xs02dA2dB2hc2c02c83c163c243c323c403c483TOP2X03SPR2A03HT12HB5Ha_st5Hl_stS3spvFS3spv1X3xs02dA2c02c83c163c243c323c403c48S2dAS3spv1X3xs02dA2c02c83c163c243c323c403c482A03A163NRAS2dA3NRAS3spv1X3xs02dA3NRA2c02c83c163c243c323c403c48S2dA3NRAS2dA3NRA2KNS2dA3NRAS1R3HIA1h3spv2lo3TOP1HSS3spv1X3xs02dA2c02c83c163c243c323c403c48S3spv1X3xs02dA2c02c83c163c243c323c403c48S2dA3NA1S3spv1X3xs02dA2c02c83c163c243c323c403c482A03A16S3spv1X3xs02dA2c02c83c163c243c323c403c482A03A16S1R2lo3LOSS2dA3NA1S2dA2KNFS3xs02dA2c02c83c163c243c323c403c48S3spv3xs02dA2dB2c02c83c163c243c323c403c482HB5Ha_st5Hl_stS3spv3xs02dA2c02c83c163c243c323c403c482HBS3xs02dA2c02c83c163c243c323c403c48S3xs02dA2c02c83c163c243c323c403c48S3xs02dA2c02c83c163c243c323c403c48S3spv3xs02dA2dB2lo2c02c83c163c243c323c403c482HB5Ha_st5Hl_stS3spv3xs02dA2lo2c02c83c163c243c323c403c484LOSPS3spv3xs02dA2lo2c02c83c163c243c323c403c48S3xs02dA2c02c83c163c243c323c403c48S3xs02dA2c02c83c163c243c323c403c48S3xs02dA2c02c83c163c243c323c403c48S3spv3xs02dA2c02c83c163c243c323c403c484SP642HB5Ha_stS3xs02dA2c02c83c163c243c323c403c482A0S3xs02dA2c02c83c163c243c323c403c48S3xs02dA2c02c83c163c243c323c403c48S3xs02dA2c02c83c163c243c323c403c48S3xs02dA2c02c83c163c243c323c403c48S3xs02dA2c02c83c163c243c323c403c48S3xs02dA2c02c83c163c243c323c403c48S3spv3xs02dA2dB2lo2c02c83c163c243c323c403c484LOSP2HB5Ha_st5Hl_stS3spv1X3xs02dA2c02c83c163c243c323c403c482X02A03AALS3xs02dA2c02c83c163c243c323c403c48". (* [comment removed for export] *)
  #[using="IMG ZF CMUL CALLOC AMC AMS JC TPV D0 NRA NRB NXA NXB BUD BUDF SLO2 C24H KCL"] Lemma mw_MID : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_W ()) "Pv,$2.Pf,$2.Phc,(3.$2;.VR,VHIA,)PLBc,(0.$1.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pc0,(4.&40.)Pc8,(4.&40.)Pc16,(4.&40.)Pc24,(4.&40.)Pc32,(4.&40.)Pc40,(4.&40.)Pc48,(4.&40.)Pxra,(4.&40.)Pxt0,(4.&40.)Pxt1,(4.&40.)Pxt2,(4.&40.)Pxa1,(4.&40.)Pxa2,(4.&40.)Pxa4,(4.&40.)Pxa5,(4.&40.)Pxa6,(4.&40.)Pxa7,(4.&40.)Pxs10,(4.&40.)Pxs11,(4.&40.)Pxt3,(4.&40.)Pxt4,(4.&40.)Pxt5,(4.&40.)Pxt6,(4.&40.)P,(8.$2;.VR,VHIA,Vh,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,+40.(34.R17.R16.R15.R14.R13.R12.R11.(3>.&40.(1<.(21.VdA,)+8.)))(35.$1.)R1=.R1<.R1;.R1:.R19.R18.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdA,R1<.R1;.R1:.R19.)P,(41.VR,VHIA,VLB,VLF,Vm,(26.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vspv,Vlo,VdB,R1=.R1<.R1;.R1:.)P,(2<.$2;.R1<.(2=.VR,)(52.$2;.VR,VHIA,Vh,)(>.&40.Vspe,)(>.&40.Vspv,)Vd1,)P,(19.R21.=)P,(19.R21.=)P,(19.(1>.R1>.)(39.VnX,VdA,VdB,))(3:.$2;.(3;.$2;.VR,VHIA,R22.Vmo,)VPOST,(3<.(3=.R17.(3>.&40.(1<.(>.&40.Vspv,)-40.))Vgp,Vtp,R16.R15.R14.Vspe,(3>.&40.(1<.(>.&40.Vspv,)-40.))(3>.&40.(1<.(21.VdB,)+:.))R13.R12.(3>.&40.(1<.(21.VdB,)+8.))R11.R10.R?.R>.Vxs2,(3>.&40.(1<.(21.VdA,)+:.))(3>.&40.(4;.(47.VR,)))Vxs5,(3>.&40.(21.VdB,))(3>.&40.VX,)(3>.&40.(21.VdA,))Vxs9,R=.R<.R;.R:.R9.R8.)VF,(3>.&40.+9>:<4.)Vfc,(3?.(4.&40.))R20.(40.$2;.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros J RA RB UW BV BF SZ.
    pose proof (JC c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dA + 8))) as JCc.
    pose proof JCc as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
    pose proof (jca_facts asegs R HIA h LB LF m dX spv lo 64 _ JCc) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    destruct (rider_view _ _ _ _ _ _ _ _ J RA NXA) as (CEA & OEA & SGA & A0 & A16 & AAL).
    xa_open J.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned spv - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold mm_fr in FR1. replace (bv_unsigned spv - 64) with (bv_unsigned spv + -64) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(bv_unsigned spv + -64, bv_unsigned spv)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OEA (md_addr dA + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 (md_n dA))) with (Z_to_bv 64 (md_n dA))
      by (unfold zx16; rewrite !unsigned_lit by (clear - NRA; lia); rewrite Z.mod_small by (clear - NRA; lia); reflexivity).
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (xa_fr_store _ _ _ _ _ _ _ _ _ _ _ c0 c8 c16 c24 c32 (Z_to_bv 64 (md_addr dB + 8)) c48 (Z_to_bv 64 (md_addr dA + 8))
                  _ _ _ _ m1 J MU WM MI1 ST1 HH1 FR1) as J1.
    pose proof (ride_fr_store dA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J RA MU WM) as RA1.
    pose proof (ride_fr_store dB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 J RB MU WM) as RB1.
    pose proof (uwc_fr_store _ _ UW MU) as UW1.
    clear J RA RB UW MU WM OEA. try clear CEA.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KN; zify_cond KN; rewrite ?Z.mod_small in KN by (clear - NRA; lia).
    { (* [comment removed for export] *)
      replace (Z_to_bv 64 (md_n dA)) with (Z_to_bv 64 0) by (f_equal; clear - KN; lia).
      eapply (mw_BENTRY 0); [exact J1| exact RA1| exact RB1| exact UW1| clear - NRA; lia| exact BV| exact BF| exact SZ]. }
    assert (NA1 : 1 <= md_n dA) by (clear - KN NRA; lia). clear KN.
    destruct (rider_view _ _ _ _ _ _ _ _ J1 RA1 NXA) as (CEA & OEA & _).
    destruct (rider_scan _ _ _ _ _ _ _ _ J1 RA1 NXA NA1) as (EBY & LENA & EP0 & OEL).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    zstep. zstep. zstep.
    replace (Z_to_bv 64 (md_p dA + md_n dA * 4 + -4)) with (Z_to_bv 64 (md_p dA + 4 * (md_n dA - 1))) by (f_equal; clear; lia).
    eapply (mw_ALOOP (Z.to_nat (md_n dA))) with (r := md_n dA);
      first [ exact J1 | exact RA1 | exact RB1 | exact UW1 | exact EBY | exact LENA | exact EP0 | exact OEL | exact BV | exact BF | exact SZ | reflexivity
            | clear - NA1 NRA; lia
            | match goal with |- ?g => idtac "MID-SIDE-LEFT:" g end ].
    all: match goal with |- ?g => idtac "MID-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End WM.
