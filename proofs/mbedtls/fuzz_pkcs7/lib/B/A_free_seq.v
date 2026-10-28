(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface Asn1Aux MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts RepRsa CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
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
Ltac2 gd_tbl_A_free_seq () : Init.string Init.list := ["Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "blkfacts"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.lb_free_mpd"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpd_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


(* [comment removed for export] *)
Definition blkfacts (L : heap_layout) (LX : list blk) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "(0.(1.$2.$2.)Lb,(1.$2.$2.)(3.(4.=(5.$2.$2.R1.))(3.(6.=(7.$2.$2.R1.))(3.(6.(8.(5.$2.$2.R1.)(7.$2.$2.R1.))(9.O2.))(:.(6.(8.(5.$2.$2.R1.)(7.$2.$2.R1.))(;.O2.))(6.(<.O2.)(5.$2.$2.R1.))))))O1.)")
(* [comment removed for export] *).

Lemma blkfacts_in : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "PL,$=.PLX,(>.$?.)PB,$2.Pk,$2.P,(10.R4.R3.)P,(11.(1.$2.$2.)(12.$2.$2.R3.R2.)R4.)(3.(4.=R4.)(3.(6.=R3.)(3.(6.(8.R4.R3.)(9.R6.))(:.(6.(8.R4.R3.)(;.R6.))(6.(<.R6.)R4.)))))")
(* [comment removed for export] *).
Proof. intros L LX B k H HIn. exact (proj1 (Forall_forall _ _) H _ HIn). Qed.

(* [comment removed for export] *)
Lemma mpdr_at_presA : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "Psegs,(>.$13.)PL,$=.Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))PLB,(>.$?.)PLB1,(>.(1.$2.$2.))PLBX,(>.$?.)PSP,$2.PX,(>.$16.)Pd,$17.P,(18.R:.R8.R6.R1.)P,(19.R;.R:.R5.R4.R3.R9.R8.)P,(1:.R<.R:.)P,(1:.R=.R:.)P,(1;.R=.R8.R7.(1<.R5.)+10.)P,(1=.R7.(1<.R6.)+10.)P,P,(1>.$1?.(20.R7.)$21.)(3.(11.(1.$2.$2.)(12.$2.$2.(22.R8.)(23.+4.(24.R8.)))R<.)(3.(1;.R10.R;.R:.(22.R8.)(23.+4.(24.R8.)))(1=.R9.(22.R8.)(23.+4.(24.R8.)))))(18.R11.R>.R<.R8.)")
(* [comment removed for export] *).
Proof.
  (intros segs L m m' LB LB1 LBX SP X d dd_H; ddestruct dd_H as (HR & HAL & HPOS & HL & HN & HO); intros HP MI MI' CR DX HH).
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply heap_presx_rw_cells; [exact HP| exact HR| cbn; exact CR| cbn; exact DX].
  - destruct (md_own d); [exact HO| |].
    + ddestruct HO as (H1 & H2 & H3 & [H4 H5]). ddestruct (HH eq_refl) as (HIN & HCR & HD).
      split; [exact H1|]. split; [exact HIN|]. split; [exact H3|]. split.
      * eapply heap_presx_bytes_at; [exact HP| exact H4| |]; rewrite u32s_length;
          replace (Z.of_nat (4 * length (md_limbs d))) with (4 * md_n d) by lia; [exact HCR| exact HD].
      * rewrite HL. eapply heap_presx_wr_at; [exact HP| rewrite <- HL; exact H5| exact HCR| exact HD].
    + ddestruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
      eapply bytes_at_static; [exact MI| exact MI'| exact H4|]. rewrite u32s_length. intros i Hi. apply H5. lia.
Qed.

(* [comment removed for export] *)
Lemma mpdr_blk_factsA : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "Psegs,(>.$13.)PL,$=.Pm,P,(14.&40.)(15.(14.&8.))PLB,(>.$?.)PLX,(>.$?.)Pd,$17.P,(18.R6.R4.R3.R1.)P,(1>.$1?.(20.R2.)$21.)P,(10.R7.R4.)P,Pb,$?.P,(11.$?.R1.R7.)(11.$?.R2.R7.)(3.(11.(1.$2.$2.)(12.$2.$2.(22.R5.)(23.+4.(24.R5.)))R7.)(3.(6.+1.(24.R5.))(3.(4.=(22.R5.))(3.(6.(8.(22.R5.)(23.+4.(24.R5.)))(9.R9.))(:.(6.(8.(22.R5.)(23.+4.(24.R5.)))(;.R9.))(6.(<.R9.)(22.R5.)))))))")
(* [comment removed for export] *).
Proof.
  (intros segs L m LB LX d dd_H; ddestruct dd_H as (HR & HAL & HPOS & HL & HN & HO); intros E BR HS). rewrite E in HO. ddestruct HO as (H1 & H2 & _).
  destruct (blkfacts_in L LX _ _ BR (HS _ H2)) as (P0 & _ & P4 & P5). auto 10.
Qed.

(* [comment removed for export] *)
Lemma lives_munchA : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "Psegs,(>.$13.)PL,$=.Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))PLB,(>.$?.)PLX,(>.$?.)Pds,(>.$17.)PW,(>.$16.)P,(0.$17.(18.R8.R6.R4.)R2.)P,(25.R2.R7.R6.)P,(26.R:.R8.R7.)P,(1:.R;.R9.)P,(1:.R<.R9.)P,(10.R<.R8.)P,Pb,$?.P,(11.$?.R1.R;.)(11.$?.R2.R;.)P,(0.$17.Ld,$17.(1=.R9.(1<.R1.)+10.)R9.)P,Pa,$2.Pn,$2.P,(4.=R2.)P,(6.(8.R3.R2.)(9.R12.))(1=.R=.R4.R3.)(0.$17.(18.R11.R>.R=.)R;.)")
(* [comment removed for export] *).
Proof.
  intros segs L m m' LB LX ds W H MU WM MI MI' HBR HS HD HW. induction ds as [|d ds IH]; [constructor|].
  inversion H; subst. inversion HD; subst. constructor; [| apply IH; assumption].
  eapply mpdr_at_munch; [eassumption| exact MU| exact WM| exact MI| exact MI'| assumption|].
  intros O. destruct (mpdr_blk_factsA _ L _ _ _ _ ltac:(eassumption) O HBR HS) as (_ & _ & I3 & I4 & _). apply HW; lia.
Qed.

(* [comment removed for export] *)
Lemma client_apart_blockA : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "PL,$=.PLBm,(>.$?.)PLBall,(>.$?.)PLF,(>.$?.)PSP,$2.PTOP,$2.PA,$2.Pn,$2.PP,$2.Pk,$2.P,(27.R:.(28.$?.R9.(29.R7.))R6.R5.R4.R3.)P,Pb,$?.P,(11.$?.R1.R;.)(11.$?.R2.R;.)P,(10.R<.(28.$?.R:.R9.))P,(2:.(28.$?.R;.R:.))P,(11.(1.$2.$2.)(12.$2.$2.R6.R5.)R<.)P,(2;.(11.(1.$2.$2.)(12.$2.$2.R7.R6.)R>.))P,(4.=R7.)P,(4.=R:.)P,(6.(9.R12.)R>.)P,(6.(;.R13.)(2<.R13.))P,(6.(2=.R14.)(<.R14.))(:.(6.(8.R?.R>.)R=.)(6.(8.R=.R<.)R?.))")
(* [comment removed for export] *).
Proof.
  intros L LBm LBall LF SP TOP A n P k CW SUB BR AP HP NIN Hk Hn ACL DI1 DI2.
  destruct (blkfacts_in L _ _ _ BR ltac:(apply in_app_iff; left; exact HP)) as (P0 & _ & P4 & P5).
  apply pointwise_apart; [exact Hn| exact Hk|]. intros a Ha C.
  destruct (CW a Ha) as [S|[[D _]|([B j] & Hb & Rr)]]; [lia| lia|].
  cbn in Rr. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
  - pose proof (SUB _ Hb) as HbL.
    assert (NE : (B, j) <> (P, k)) by (intros E; rewrite E in Hb; exact (NIN Hb)).
    destruct (blocks_apart_neq _ (B, j) (P, k) AP ltac:(apply in_app_iff; left; exact HbL) ltac:(apply in_app_iff; left; exact HP) NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
  - ddestruct (in_fdata_hull LF (B, j) a Hb ltac:(cbn; lia)) as ([FB w] & HF & Hr2). cbn in Hr2.
    destruct (blocks_apart_app_lr LBall LF P k FB w AP HP HF); lia.
Qed.

Section FreeSeqA.
Variable segs : list Segment.
Variable R : art_layout.
#[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
Local Notation L := (arl_L R).
Variables (LBall LF LBf : list blk) (SP TOP A sz : Z) (FR : list mpd).
Hypothesis HBR : blkfacts L (LBall ++ LF).
Hypothesis HAP : blocks_apart (LBall ++ LF).
Hypothesis CW : client_wrange L (LBf ++ fdata LF) SP TOP A sz.
Hypothesis ACL : alloc_ceiling <= SP.
Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
Hypothesis FF1 : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "Pd,$17.P,(11.$17.R1.VFR,)P,(1>.$1?.(20.R2.)$21.)(3.(11.(1.$2.$2.)(12.$2.$2.(22.R3.)(23.+4.(24.R3.)))VLBall,)(3.(6.+1.(24.R3.))(3.(4.=(22.R3.))(3.(6.(8.(22.R3.)(23.+4.(24.R3.)))(9.(2>.VR,)))(:.(6.(8.VA,Vsz,)(22.R3.))(6.(8.(22.R3.)(23.+4.(24.R3.)))VA,))))))")
(* [comment removed for export] *).
Hypothesis FF2 : mpds_apart FR.

(* [comment removed for export] *)
#[using="TOP HBR HAP CW FF1 FF2"] Lemma live_after_freeA : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))PLBc,(>.$?.)Pd0,$17.Pd,$17.P,Pb,$?.P,(11.$?.R1.R4.)(11.$?.R2.VLBall,)P,Pb,$?.P,(11.$?.R1.VLBf,)(11.$?.R2.(2?.R5.R6.))P,(11.$17.R4.VFR,)P,(6.VA,(1<.R5.))P,(6.(8.(1<.R6.)+10.)(8.VA,Vsz,))P,(19.Vsegs,(2>.VR,)(28.$?.(2?.R7.R8.)(29.VLF,))VSP,(30.R7.)R:.R9.)P,(1:.Vsegs,R;.)P,(1:.Vsegs,R;.)P,(18.Vsegs,R=.R;.R9.)P,P,(1>.$1?.(20.R:.)$21.)(11.$17.R;.VFR,)P,(6.VA,(1<.R;.))P,(6.(8.(1<.R<.)+10.)(8.VA,Vsz,))P,(:.(6.(8.(1<.R=.)+10.)(1<.R>.))(6.(8.(1<.R>.)+10.)(1<.R=.)))(18.Vsegs,R11.(2?.R?.R10.)R>.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBc d0 d SUB0 SUBm Hd0 B1 B2 PX MI MI' Md HdF C1 C2 DJ.
  eapply mpdr_at_presA; [exact Md| exact PX| exact MI| exact MI'| | |].
  - eapply client_range_of_wrange; [exact CW| apply lb_sub_app; exact SUBm| lia| lia| lia].
  - cbn. split; [lia|]. destruct (md_own d0) eqn:O0; cbn; [exact I| | exact I].
    ddestruct (FF1 d0 Hd0 O0) as (_ & _ & _ & _ & ?). lia.
  - intros O. destruct (mpdr_blk_factsA _ L _ _ _ _ Md O HBR ltac:(intros b Hb; apply in_app_iff; left; apply SUB0, Hb)) as (I1 & I2 & I3 & I4 & I5).
    ddestruct (FF1 d (HdF O) O) as (J1 & _ & _ & _ & J5).
    assert (KEEP : In (md_p d, 4 * md_n d) (lb_free_mpd d0 LBc)).
    { apply lb_free_mpd_keep; [exact I1|]. intros O0. apply (FF2 d d0); auto. lia. }
    split; [exact KEEP|]. split.
    + intros x Hx. right; right. exists (md_p d, 4 * md_n d). split; [apply in_app_iff; left; exact KEEP| cbn; lia].
    + cbn. split; [lia|]. destruct (md_own d0) eqn:O0; cbn; [exact I| | exact I].
      ddestruct (FF1 d0 Hd0 O0) as (K1 & K2 & _ & _ & _).
      pose proof (FF2 d d0 (HdF O) Hd0 ltac:(lia) O O0) as NE.
      destruct (blocks_apart_neq _ _ _ HAP ltac:(apply in_app_iff; left; exact J1) ltac:(apply in_app_iff; left; exact K1)
                  ltac:(intros E; injection E; intros; exact (NE ltac:(assumption))) ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
Qed.

(* [comment removed for export] *)
#[using="LBall TOP CW FF1"] Lemma chunk_after_freeA : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))PLBc,(>.$?.)Pd0,$17.Pa,$2.Pcs,(>.$31.)Psp,$2.P,Pb,$?.P,(11.$?.R1.VLBf,)(11.$?.R2.(2?.R6.R7.))P,(11.$17.R5.VFR,)P,(6.VA,(1<.R6.))P,(6.(8.(1<.R7.)+10.)(8.VA,Vsz,))P,(19.Vsegs,(2>.VR,)(28.$?.(2?.R8.R9.)(29.VLF,))R5.(30.R8.)R;.R:.)P,(6.R6.VSP,)P,(6.(9.(2>.VR,))R7.)P,(32.Vsegs,R>.R:.R9.)P,(:.(3.(6.VA,R;.)(6.(8.R;.(33.(34.R:.)))(8.VA,Vsz,)))(6.R9.R;.))P,(:.(6.(8.R<.(33.(34.R;.)))(1<.R=.))(6.(8.(1<.R=.)+10.)R<.))(32.Vsegs,R10.R=.R<.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBc d0 a cs sp SUBm Hd0 B1 B2 PX HSP ACLs H WH DJ.
  eapply heap_presx_rw_cells; [exact PX| exact H| |].
  - destruct WH as [WH|WH]; [eapply client_range_of_wrange; [exact CW| apply lb_sub_app; exact SUBm| lia| lia| lia]|]. intros x Hx. left. lia.
  - cbn. split; [lia|]. destruct (md_own d0) eqn:O0; cbn; [exact I| | exact I].
    ddestruct (FF1 d0 Hd0 O0) as (_ & _ & _ & ? & ?). lia.
Qed.

#[using="TOP HBR HAP CW FF1 FF2"] Lemma lives_after_freeA : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))PLBc,(>.$?.)Pd0,$17.Pds,(>.$17.)P,Pb,$?.P,(11.$?.R1.R4.)(11.$?.R2.VLBall,)P,Pb,$?.P,(11.$?.R1.VLBf,)(11.$?.R2.(2?.R5.R6.))P,(11.$17.R4.VFR,)P,(6.VA,(1<.R5.))P,(6.(8.(1<.R6.)+10.)(8.VA,Vsz,))P,(19.Vsegs,(2>.VR,)(28.$?.(2?.R7.R8.)(29.VLF,))VSP,(30.R7.)R:.R9.)P,(1:.Vsegs,R;.)P,(1:.Vsegs,R;.)P,(0.$17.(18.Vsegs,R=.R;.)R9.)P,(0.$17.Ld,$17.(3.P,(1>.$1?.(20.R1.)$21.)(11.$17.R2.VFR,)(3.(6.VA,(1<.R1.))(3.(6.(8.(1<.R1.)+10.)(8.VA,Vsz,))(:.(6.(8.(1<.R1.)+10.)(1<.R<.))(6.(8.(1<.R<.)+10.)(1<.R1.))))))R:.)(0.$17.(18.Vsegs,R>.(2?.R<.R=.))R;.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBc d0 ds SUB0 SUBm Hd0 B1 B2 PX MI MI' H1 H2. induction ds as [|d ds IH]; [constructor|].
  inversion H1; subst. inversion H2 as [|? ? (Q1 & Q2 & Q3 & Q4) Q5]; subst. constructor; [| apply IH; assumption].
  eapply live_after_freeA; eauto.
Qed.

#[using="LBall TOP CW FF1"] Lemma chunks_after_freeA : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))PLBc,(>.$?.)Pd0,$17.PCS,(>.(1.$2.(>.$31.)))Psp,$2.P,Pb,$?.P,(11.$?.R1.VLBf,)(11.$?.R2.(2?.R5.R6.))P,(11.$17.R4.VFR,)P,(6.VA,(1<.R5.))P,(6.(8.(1<.R6.)+10.)(8.VA,Vsz,))P,(19.Vsegs,(2>.VR,)(28.$?.(2?.R7.R8.)(29.VLF,))R5.(30.R7.)R:.R9.)P,(6.R6.VSP,)P,(6.(9.(2>.VR,))R7.)P,(0.(1.$2.(>.$31.))Lac,(1.$2.(>.$31.))(32.Vsegs,R>.(5.$2.(>.$31.)R1.)(7.$2.(>.$31.)R1.))R9.)P,(0.(1.$2.(>.$31.))Lac,(1.$2.(>.$31.))(3.(:.(3.(6.VA,(5.$2.(>.$31.)R1.))(6.(8.(5.$2.(>.$31.)R1.)(33.(34.(7.$2.(>.$31.)R1.))))(8.VA,Vsz,)))(6.R:.(5.$2.(>.$31.)R1.)))(:.(6.(8.(5.$2.(>.$31.)R1.)(33.(34.(7.$2.(>.$31.)R1.))))(1<.R<.))(6.(8.(1<.R<.)+10.)(5.$2.(>.$31.)R1.))))R:.)(0.(1.$2.(>.$31.))Lac,(1.$2.(>.$31.))(32.Vsegs,R?.(5.$2.(>.$31.)R1.)(7.$2.(>.$31.)R1.))R;.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBc d0 CS sp SUBm Hd0 B1 B2 PX HSP ACLs H1 H2. induction CS as [|ac CS IH]; [constructor|].
  inversion H1; subst. inversion H2 as [|? ? [Q1 Q2] Q3]; subst. constructor; [| apply IH; assumption].
  eapply chunk_after_freeA; eauto.
Qed.

(* [comment removed for export] *)
#[using="HBR HAP ACL DIMG"] Lemma presA_free_fp : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "PLB1,(>.$?.)Psp,$2.PSSP,$2.PTOPs,$2.PX,(>.$16.)Pd,$17.Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))P,(35.Vsegs,VR,R8.VLF,R7.R6.R5.(30.R3.)R2.R1.)P,Pb,$?.P,(11.$?.R1.VLBf,)(11.$?.R2.R;.)P,Pb,$?.P,(11.$?.R1.VLBf,)(11.$?.R2.VLBall,)P,(6.VSP,R:.)P,P,(1>.$1?.(20.R7.)$21.)(3.(11.(1.$2.$2.)(12.$2.$2.(22.R8.)(23.+4.(24.R8.)))VLBall,)(3.(2;.(11.(1.$2.$2.)(12.$2.$2.(22.R8.)(23.+4.(24.R8.)))VLBf,))(6.+1.(24.R8.))))P,Pa,$2.P,(36.R:.R1.)(2;.(3.(6.(1<.R:.)R2.)(4.R2.(8.(1<.R:.)+10.))))(35.Vsegs,VR,VLBf,VLF,R=.R<.R;.R:.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros LB1 sp SSP TOPs X d m m' [PX S] S1 S0 HSP HB HX. split.
  - intros a Ha Hc Ho. apply PX; [exact Ha| |].
    + destruct Hc as [C|[C|(b & Hb & C)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [| exact C]].
      apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply S1, Hb| right; exact Hb].
    + cbn. split; [pose proof (HX a Ho); lia|]. destruct (md_own d) eqn:O; cbn; [exact I| | exact I]. split; [| exact I].
      ddestruct (HB eq_refl) as (I1 & I2 & I3). intros IN.
      destruct (blkfacts_in L _ _ _ HBR ltac:(apply in_app_iff; left; exact I1)) as (B0 & _ & B4 & B5).
      destruct Hc as [C|[C|([b k] & Hb & C)]]; [lia| destruct DIMG; lia|]. cbn in C.
      apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      * assert (NE : (b, k) <> (md_p d, 4 * md_n d)) by (intros E; rewrite E in Hb; exact (I2 Hb)).
        destruct (blocks_apart_neq _ _ _ HAP ltac:(apply in_app_iff; left; exact (S0 _ Hb)) ltac:(apply in_app_iff; left; exact I1) NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
      * ddestruct (in_fdata_hull LF (b, k) a Hb ltac:(cbn; lia)) as ([FB w] & HF & Hr2). cbn in Hr2.
        destruct (blocks_apart_app_lr LBall LF (md_p d) (4 * md_n d) FB w HAP I1 HF); lia.
  - intros c Hc Hr. apply S; [| exact Hr].
    destruct Hc as [H|[(b & Hb & Hx)|[H|H]]]; [left; exact H| right; left; exists b; split; [apply S1, Hb| exact Hx]| right; right; left; exact H| right; right; right; exact H].
Qed.
End FreeSeqA.

(* [comment removed for export] *)
Lemma free_facts_introA : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "Psegs,(>.$13.)PR,$37.PHIA,(38.R2.R1.)Ph,(39.R3.R2.R1.)PLBall,(>.$?.)PLF,(>.$?.)PLBf,(>.$?.)Pm,P,(14.&40.)(15.(14.&8.))PSP,$2.PTOP,$2.PA,$2.Psz,$2.PFR,(>.$17.)P,(3:.R=.R<.R;.R:.R9.R8.R6.)P,(3;.$2.(3<.(1.$2.$2.)$2.(5.$2.$2.)R:.))P,Pd,$17.P,(11.$17.R1.R4.)(18.R11.R:.R=.R2.)P,(27.(2>.R?.)(28.$?.R:.(29.R;.))R8.R7.R6.R5.)P,Pb,$?.P,(11.$?.R1.R<.)(11.$?.R2.R?.)P,Pd,$17.P,(11.$17.R1.R7.)P,(1>.$1?.(20.R2.)$21.)(2;.(11.(1.$2.$2.)(12.$2.$2.(22.R3.)(23.+4.(24.R3.)))R?.))P,(6.(9.(2>.R12.))R;.)P,(4.=R9.)P,(6.(;.(2>.R14.))(2<.(2>.R14.)))P,(6.(2=.(2>.R15.))(<.(2>.R15.)))Pd,$17.P,(11.$17.R1.R<.)P,(1>.$1?.(20.R2.)$21.)(3.(11.(1.$2.$2.)(12.$2.$2.(22.R3.)(23.+4.(24.R3.)))R16.)(3.(6.+1.(24.R3.))(3.(4.=(22.R3.))(3.(6.(8.(22.R3.)(23.+4.(24.R3.)))(9.(2>.R19.)))(:.(6.(8.R10.R?.)(22.R3.))(6.(8.(22.R3.)(23.+4.(24.R3.)))R10.))))))")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LBall LF LBf m SP TOP A sz FR HH ND HM CW SUB NI ACL SZ DI1 DI2 d Hd O.
  destruct (hm_apart segs R HIA h LBall LF m HH) as [HBR HAP].
  destruct (mpdr_blk_factsA _ (arl_L R) _ _ _ _ (HM d Hd) O HBR ltac:(intros b Hb; apply in_app_iff; left; exact Hb)) as (I1 & I2 & I3 & I4 & I5).
  refine (conj I1 (conj I2 (conj I3 (conj I4 _)))).
  eapply (client_apart_blockA (arl_L R) LBf LBall LF); try eassumption; try lia. apply NI; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section STEP.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Variable ENTRY : Z.
  Hypothesis SPF : mpi_free_stmtA asegs R HIA ENTRY.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.

  #[using="SPF NEEDR DIMG"] Lemma free_stepA : ltac2:(CDefT.buildp (gd_tbl_A_free_seq ()) "Pra,(14.&40.)Psp,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa0,(14.&40.)Pa1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PF,(3=.&5.(14.&40.))Pfc,(14.&20.)PPOST,P,$3>.SpPm0,P,(14.&40.)(15.(14.&8.))Pmc,P,(14.&40.)(15.(14.&8.))Pmo0,$3?.Ph0,(39.$40.VR,VHIA,)Phc,(39.$40.VR,VHIA,)PLBall,(>.$?.)PLF,(>.$?.)PLBf,(>.$?.)PLBc,(>.$?.)PSP,$2.PA,$2.Psz,$2.Plo,$2.Pd,$2.PVB,$2.PFB,$2.PFR,(>.$17.)Pd0,$17.Prest,(>.$17.)PCS,(>.(1.$2.(>.$31.)))PX0,$2.P,(3:.$40.VR,VHIA,R11.R=.R?.R14.)P,(1>.$2.(41.$40.VR,VHIA,R12.)(41.$40.VR,VHIA,R13.))P,(1>.$2.(42.$40.VR,VHIA,R13.)(42.$40.VR,VHIA,R14.))P,(1>.$2.(43.$40.VR,VHIA,R14.)(43.$40.VR,VHIA,R15.))P,Px,$2.P,(44.$40.VR,VHIA,R17.R1.)(44.$40.VR,VHIA,R17.R2.)P,(1>.$2.(1<.R9.)R6.)P,(10.(2>.VR,)(28.$?.R16.R15.))P,(2:.(28.$?.R17.R16.))P,(27.(2>.VR,)(28.$?.R16.(29.R17.))R14.(41.$40.VR,VHIA,R1:.)R13.R12.)P,Pd,$17.P,(11.$17.R1.R?.)P,(1>.$1?.(20.R2.)$21.)(3.(11.(1.$2.$2.)(12.$2.$2.(22.R3.)(23.+4.(24.R3.)))R1<.)(3.(6.+1.(24.R3.))(3.(4.=(22.R3.))(3.(6.(8.(22.R3.)(23.+4.(24.R3.)))(9.(2>.VR,)))(:.(6.(8.R17.R16.)(22.R3.))(6.(8.(22.R3.)(23.+4.(24.R3.)))R17.))))))P,(45.R?.)P,Pb,$?.P,(11.$?.R1.R1:.)(11.$?.R2.R1=.)P,Pb,$?.P,(11.$?.R1.R1;.)(11.$?.R2.(2?.R12.R1;.))P,Pb,$?.P,(11.$?.R1.R1;.)(11.$?.R2.R1?.)P,P,(1>.$1?.(20.R12.)$21.)(2;.(11.(1.$2.$2.)(12.$2.$2.(22.R13.)(23.+4.(24.R13.)))R1=.))P,(11.$17.R13.R14.)P,(6.R1;.R11.)P,(6.(8.R12.+10.)(8.R1<.R1;.))P,(2;.(1>.$1?.(20.R16.)$46.))P,(0.$17.(18.$40.R27.R20.)(47.$17.R17.R16.))P,(0.$17.Ld,$17.(3.P,(1>.$1?.(20.R1.)$21.)(11.$17.R2.R1;.)(3.(6.R20.(1<.R1.))(3.(6.(8.(1<.R1.)+10.)(8.R20.R1?.))(:.(6.(8.(1<.R1.)+10.)R16.)(6.(8.R16.+10.)(1<.R1.))))))R17.)P,(0.(1.$2.(>.$31.))Lac,(1.$2.(>.$31.))(32.$40.R2:.(5.$2.(>.$31.)R1.)(7.$2.(>.$31.)R1.))R17.)P,(0.(1.$2.(>.$31.))Lac,(1.$2.(>.$31.))(3.(:.(3.(6.R22.(5.$2.(>.$31.)R1.))(6.(8.(5.$2.(>.$31.)R1.)(33.(34.(7.$2.(>.$31.)R1.))))(8.R22.R21.)))(6.(48.&40.R4=.)(5.$2.(>.$31.)R1.)))(:.(6.(8.(5.$2.(>.$31.)R1.)(33.(34.(7.$2.(>.$31.)R1.))))R18.)(6.(8.R18.+10.)(5.$2.(>.$31.)R1.))))R18.)P,(49.$40.VR,VHIA,R29.R25.R26.R23.(4:.VR,)(47.(1.$2.$2.)(12.$2.$2.R22.(8.R22.R21.))(4;.(1.$2.$2.)))R2<.R2;.)P,(4<.$40.(4=.VR,)(44.$40.VR,VHIA,R2:.)R2<.R23.R22.)P,(4>.$40.R2=.R22.(48.&40.R4?.))P,(6.R23.(4?.(4?.(48.&40.R50.)+40.)(50.VR,)))P,(6.(4:.VR,)R24.)P,(6.(48.&40.R52.)R28.)P,(6.R29.(41.$40.VR,VHIA,R2?.))P,(1>.$2.(51.(48.&40.R54.)+10.)=)P,(1>.(14.&40.)R53.(52.&40.(53.VR,)))P,(1:.$40.R34.)P,(6.(54.$40.VR,VHIA,R32.)R28.)P,(6.(8.R29.$55.)$56.)P,(57.VR,R2>.R2=.R2;.)P,(6.(58.$40.VR,VHIA,R35.)R2:.)P,(6.(8.R2;.(59.R2=.))$5:.)P,(1>.(14.&40.)R54.(52.&40.R27.))P,Pt0',(14.&40.)Pt1',(14.&40.)Pt2',(14.&40.)Pa0',(14.&40.)Pa1',(14.&40.)Pa2',(14.&40.)Pa3',(14.&40.)Pa4',(14.&40.)Pa5',(14.&40.)Pa6',(14.&40.)Pa7',(14.&40.)Pt3',(14.&40.)Pt4',(14.&40.)Pt5',(14.&40.)Pt6',(14.&40.)Pm2,P,(14.&40.)(15.(14.&8.))Ph2,(39.$40.VR,VHIA,)P,(3:.$40.VR,VHIA,R1.(2?.R3<.R45.)R47.R2.)P,(1>.$2.(41.$40.VR,VHIA,R2.)(41.$40.VR,VHIA,R4;.))P,(1>.$2.(42.$40.VR,VHIA,R3.)(42.$40.VR,VHIA,R4<.))P,(1>.$2.(43.$40.VR,VHIA,R4.)(43.$40.VR,VHIA,R4=.))P,Px,$2.P,(44.$40.VR,VHIA,R4?.R1.)(44.$40.VR,VHIA,R7.R2.)P,(6.(54.$40.VR,VHIA,R6.)(8.R44.$55.))P,(6.(58.$40.VR,VHIA,R7.)(8.R44.(59.R46.)))P,(0.$17.(18.$40.R9.(2?.R43.R4<.))R42.)P,(0.(1.$2.(>.$31.))Lac,(1.$2.(>.$31.))(32.$40.R;.(5.$2.(>.$31.)R1.)(7.$2.(>.$31.)R1.))(47.(1.$2.(>.$31.))(12.$2.(>.$31.)R41.(5;.=(52.&40.+1.)=(5<.R44.)))R42.))P,(49.$40.VR,VHIA,R53.R4?.R50.R4=.(4:.VR,)(47.(1.$2.$2.)(12.$2.$2.R4<.(8.R4<.R4;.))(4;.(1.$2.$2.)))R56.R;.)P,(4<.$40.(4=.VR,)(44.$40.VR,VHIA,R54.)R<.R4=.R4<.)P,(4>.$40.R=.R4<.(48.&40.R79.))P,(1:.$40.R>.)(5=.$40.(5>.$40.VR,VHIA,R>.R58.)R5;.(5?.(60.R7<.R7;.R7:.R79.R1>.R1=.R1<.R75.R74.R1;.R1:.R19.R18.R17.R16.R15.R14.R6;.R6:.R69.R68.R67.R66.R65.R64.R63.R62.R13.R12.R11.R10.)R5=.(61.R7<.)R5<.(62.(14.&40.))R?.(63.$40.)))(5=.$40.(5>.$40.VR,VHIA,R39.R3;.)R3>.(5?.(60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.)R40.(52.&40.VENTRY,)R3?.(62.(14.&40.))R3<.(63.$40.)))")
(* [comment removed for export] *).
  Proof.
    intros until X0. intros HH HTc HSc HFc HCSc E0 HBR HAP CW FF1 FF2 SUBF SUBf SUBc NI IN B1 B2 OWN LIV LIVS CH CHS PXA OBJ
           ST LO LOS SPle SPT SPA TP MI HV HVB UWO HFR HFB -> K.
    ddestruct PXA as (PXA & PW1 & PW2 & PW3).
    pose proof DIMG as [DI1 DI2]. pose proof (art_lo asegs R HIA) as ALO.
    assert (ACLs : alloc_ceiling <= bv_unsigned sp) by (clear - ALO LOS LO NEEDR; lia).
    assert (ACLS : alloc_ceiling <= SP) by (clear - ACLs SPle; lia).
    pose proof (hcs_ok asegs R HIA h0) as CSOK0.
    pose proof (Forall_inv LIV) as M0. unfold mpdr_at in M0. rewrite E0 in M0.
    pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_free_stmtA in SPF.
      eapply SPF with (lo := lo) (h := hc) (LB := LBc) (LF := LF) (d := d);
        [ exact HH | exact HK1 | exact M0 | exact OWN | | | exact ST | exact LOS | exact LO | rewrite HTc; clear - SPle SPT; lia | exact SPA | exact TP | exact MI
        | | | | | reflexivity ].
      - change (mpi_free_LB (md_own d0) (md_p d0) (md_n d0) LBc) with (lb_free_mpd d0 LBc). rewrite HTc.
        eapply (client_wrange_weak L); [exact CW| apply lb_sub_app; exact SUBf| exact SPle| exact B1| exact B2].
      - intros O. ddestruct (FF1 d0 IN O) as (_ & _ & _ & _ & ?). clear - H B1 B2. lia.
      - eapply aobj_sub; [eapply aobj_cs_mono; [exact HCSc| exact OBJ]| exact B1| exact B2].
      - clear - HV HVB. lia.
      - eapply uw_obj_sub; [exact UWO| exact B1| exact B2].
      - clear - HFR HFB. lia. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_free_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PX & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & CHX).
    change (mpi_free_LB (md_own d0) (md_p d0) (md_n d0) LBc) with (lb_free_mpd d0 LBc) in HH2, PX.
    change ((X0, X0 + 16) :: mpi_free_X (md_own d0) (md_p d0) (md_n d0))
      with (mpd_fp (mkMPD X0 (md_sg d0) (md_n d0) (md_p d0) (md_limbs d0) (md_pad d0) (md_own d0))) in PX.
    assert (EFP : mpd_fp (mkMPD X0 (md_sg d0) (md_n d0) (md_p d0) (md_limbs d0) (md_pad d0) (md_own d0)) = mpd_fp d0) by (unfold mpd_fp; cbn; rewrite E0; reflexivity).
    rewrite EFP in PX. clear EFP. rewrite HSc in PX.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ PX) as PXh.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    apply (K y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m2 h2 HH2
             ltac:(rewrite HT2; exact HTc) ltac:(rewrite HS2; exact HSc) ltac:(rewrite HF2; exact HFc)
             ltac:(intros x Hx; apply HCS2, HCSc, Hx) ltac:(clear - HV HV2; lia) ltac:(clear - HFR HFR2; lia)).
    - eapply (lives_after_freeA asegs R LBall LF LBf SP _ A sz FR) with (m := mc) (d0 := d0);
        [exact HBR| exact HAP| exact CW| exact FF1| exact FF2| exact SUBc| exact SUBf| exact IN| clear - B1 E0; lia| clear - B2 E0; lia| | exact MI| exact MI2| exact (Forall_inv_tail LIV)|].
      + eapply (MpiFacts.heap_presx_weaken asegs L); [exact PXh| exact SPle| intros x Hx; exact Hx].
      + eapply Forall_impl; [| exact LIVS]. cbn. (intros dd dd_H; ddestruct dd_H as (Q1 & Q2 & Q3 & Q4)). rewrite E0. auto.
    - apply Forall_cons; [exact CHX|].
      eapply (chunks_after_freeA asegs R LBall LF LBf SP _ A sz FR) with (m := mc) (d0 := d0) (sp := bv_unsigned sp);
        [exact CW| exact FF1| exact SUBf| exact IN| clear - B1 E0; lia| clear - B2 E0; lia| exact PXh| exact SPle| exact ACLs| exact CH|].
      eapply Forall_impl; [| exact CHS]. cbn -[Z.add Z.le Z.of_nat]. intros ac [Q1 Q2]. rewrite E0. auto.
    - split; [| exact (conj PW1 (conj PW2 PW3))].
      eapply presA_trans; [exact PXA|].
      eapply (presA_weaken asegs R LBf LBf LF LF (bv_unsigned sp) SP (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA h0) (hstkhi asegs R HIA h0) [(A, A + sz)] [(A, A + sz)]);
        [| intros b Hb; exact Hb| intros b Hb; exact Hb| exact SPle| clear; lia| clear; lia| intros x Hx; exact Hx].
      eapply (presA_free_fp asegs R LBall LF LBf (bv_unsigned sp)) with (LB1 := lb_free_mpd d0 LBc) (d := d0);
        [exact HBR| exact HAP| exact ACLs| exact DIMG| exact PX| exact SUBf| exact SUBF| clear; lia| | intros a Ha; cbn in Ha; rewrite E0; clear - Ha B1 B2; lia].
      intros O. ddestruct (FF1 d0 IN O) as (I1 & I2 & _). split; [exact I1|]. split; [exact (NI O)| exact I2].
    - eapply (presA_aobj asegs R (hcs asegs R HIA h0)); [exact CSOK0| exact PX| exact OBJ| | clear - LOS LO NEEDR; lia| intros x Hx; eapply hcs_below_top; exact Hx].
      eapply client_range_of_wrange; [exact CW| apply lb_sub_app; exact SUBf| exact SPle| clear; lia| clear; lia].
    - exact ST2.
    - exact MI2.
  Qed.
End STEP.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fsA_post HH HTc HSc HFc HCSc HV HFR LIV CH PXA OBJ ST MI :=
  let h0 := lazymatch type of PXA with presW _ _ _ ?h0 _ _ _ _ _ _ _ => h0 end in
  clear HH HTc HSc HFc HCSc HV HFR LIV CH PXA OBJ ST MI;
  repeat match goal with
         | H : ainv_laws _ _ |- _ => clear H | H : kinv_laws _ _ _ |- _ => clear H
         | H : cs_ok _ (hcs _ _ _ ?hx) |- _ => lazymatch hx with h0 => fail | _ => clear H end
         | H : aobj _ _ (hcs _ _ _ ?hx) _ _ _ |- _ => lazymatch hx with h0 => fail | _ => clear H end
         | H : crange (hcs _ _ _ ?hx) _ _ |- _ => lazymatch hx with h0 => fail | _ => clear H end
         end;
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HH HTc HSc HFc HCSc HV HFR LIV CH PXA OBJ ST MI;
  lazymatch type of HH with HM _ ?R ?HIA ?h2 _ _ _ =>
    let LAWS := fresh "LAWS" in let KINV := fresh "KINV" in let CSOKc := fresh "CSOKc" in let OBJc := fresh "OBJc" in let SCSc := fresh "SCSc" in
    pose proof (AIh_laws asegs R HIA h2) as LAWS;
    lazymatch goal with |- aevtA _ (KF _ _ _ _ ?mo0) _ _ => pose proof (KF_kinv asegs R HIA h2 mo0) as KINV end;
    pose proof (hcs_ok asegs R HIA h2) as CSOKc;
    pose proof (aobj_cs_mono asegs _ _ _ _ _ _ HCSc OBJ) as OBJc;
    try match goal with SCS : crange (hcs _ _ _ h0) ?lo ?k |- _ => pose proof (crange_mono _ _ lo k HCSc SCS) as SCSc end
  end;
  try (rewrite unsigned_lit in ST by lia);
  try (lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).

(* [comment removed for export] *)
Ltac inl := solve [repeat (first [left; reflexivity| right])].

(* [comment removed for export] *)
Ltac fa_nth H n := lazymatch n with O => constr:(Forall_inv H) | S ?k => let H' := constr:(Forall_inv_tail H) in fa_nth H' k end.
Ltac fa_get H n name := let t := fa_nth H n in pose proof t as name; cbn [fst snd] in name.

(* [comment removed for export] *)
Ltac fsA_in := cbn; inl.
Ltac fsA_addr := cbn [md_addr mpd_z mpd_zero mpd_init].

(* [comment removed for export] *)
Ltac fsA_side spo restF :=
  rewrite ?(unsigned_lit spo) by lia;
  lazymatch goal with
  | |- HM _ _ _ _ _ _ _ => eassumption
  | |- htop _ _ _ _ = _ => first [eassumption | reflexivity]
  | |- hstkhi _ _ _ _ = _ => first [eassumption | reflexivity]
  | |- hflag _ _ _ _ = _ => first [eassumption | reflexivity]
  | |- forall x, hcs _ _ _ _ x -> hcs _ _ _ _ x => first [eassumption | intros x Hx; exact Hx]
  | |- md_addr _ = _ => first [eassumption | reflexivity | fsA_addr; first [reflexivity | lia]]
  | |- blkfacts _ _ => eassumption
  | |- blocks_apart _ => eassumption
  | |- client_wrange _ _ _ _ _ _ => eassumption
  | |- forall d, In d _ -> md_own d = LHeap -> In _ _ /\ _ => eassumption
  | |- mpds_apart _ => eassumption
  | |- forall b, In b _ -> In b _ =>
      first [ eassumption
            | intros b Hb; exact (lb_free_mpds_sub restF _ b Hb)
            | intros b Hb; do 16 (try (apply lb_free_mpd_sub in Hb)); first [exact Hb | apply lb_free_mpds_sub in Hb; exact Hb] ]
  | |- md_own _ = LHeap -> ~ In _ _ =>
      match goal with NI : forall d, In d _ -> md_own d = LHeap -> ~ In _ _ |- _ => intros O; apply NI; [fsA_in| exact O] end
  | |- In _ _ => fsA_in
  | |- md_own _ <> LStatic =>
      first [ assumption | cbn; discriminate
            | match goal with FRB : Forall mpd_freeable _ |- _ => refine (proj1 (Forall_forall _ _) FRB _ _); fsA_in end ]
  | |- Forall (mpdr_at _ _ _) _ => eassumption
  | |- Forall (fun ac => rw_cells _ _ (fst ac) (snd ac)) _ => eassumption
  | |- Forall _ _ =>
      repeat apply Forall_cons; try apply Forall_nil;
      first [ (* [comment removed for export] *) split; [ first [ intros _; fsA_in
                                             | match goal with KEPT : Forall (fun d => md_own d <> LHeap) _ |- _ =>
                                                 intros O; exfalso; eapply (proj1 (Forall_forall _ _) KEPT); [| exact O]; fsA_in end ]
                                     | fsA_addr; lia ]
            | (* [comment removed for export] *) cbn [fst snd cells_size csize Nat.add mpi_cells length]; fsA_addr; lia ]
  | |- presW _ _ _ _ _ _ _ _ _ _ _ => eassumption
  | |- aobj _ _ _ _ _ _ => eassumption
  | |- stk _ _ _ _ => eassumption
  | |- mem_inv _ _ => eassumption
  | |- _ = Z_to_bv 64 _ => first [assumption | reflexivity | fsA_addr; reflexivity | f_equal; fsA_addr; lia]
  | |- uw_obj _ _ _ _ => first [eassumption | eapply uw_obj_sub; [eassumption| fsA_addr; lia| fsA_addr; lia]]
  | |- havol _ _ _ _ <= _ => eassumption
  | |- hfr _ _ _ _ <= _ => eassumption
  | |- _ => first [assumption | fsA_addr; lia | unfold AVOL_CALL, fr_charge in *; lia | match goal with |- ?g => idtac "fsA_side UNSOLVED:" g end]
  end.
