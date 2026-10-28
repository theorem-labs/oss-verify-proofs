(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_client2 () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Stdlib.Lists.List.In"; "Stdlib.Lists.List.flat_map"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.or"; "remove_nth"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.app"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_ceil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "MCA.struct_locA"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "MCA.local_okA"; "RocqVerifyHarness.AgentSubmission.Spec.MpiClient.structs_apart"; "RocqVerifyHarness.AgentSubmission.Spec.MpiClient.limbs_apart"; "MCA.w_blk_okA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "MCA.chunk_okA"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "MCA.wx_ok"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "MCA.cstateA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.binop_keep"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiClient.set_nth"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "Corelib.Init.Datatypes.length"; "MCA.wl_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"].


(* [comment removed for export] *)
Fixpoint remove_nth {A} (i : nat) (l : list A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: t, O => t
  | x :: t, S k => x :: remove_nth k t
  end.

Lemma In_remove_nth {A} : forall i (l : list A) y, In y (remove_nth i l) -> In y l.
Proof. induction i; intros [|x t] y H; cbn in *; try tauto. destruct H as [<-|H]; [left; reflexivity| right; eauto]. Qed.

Lemma nth_error_nil' {A} : forall k, nth_error (@nil A) k = None.
Proof. destruct k; reflexivity. Qed.

Lemma nth_error_remove_nth {A} : forall i j (l : list A),
  nth_error (remove_nth i l) j = nth_error l (if (j <? i)%nat then j else S j).
Proof.
  induction i; intros j [|x t].
  - change (remove_nth 0 (@nil A)) with (@nil A). rewrite !nth_error_nil'. reflexivity.
  - change (remove_nth 0 (x :: t)) with t. replace (j <? 0)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
  - change (remove_nth (S i) (@nil A)) with (@nil A). rewrite !nth_error_nil'. reflexivity.
  - change (remove_nth (S i) (x :: t)) with (x :: remove_nth i t). destruct j as [|j'].
    + reflexivity.
    + change (nth_error (x :: remove_nth i t) (S j')) with (nth_error (remove_nth i t) j'). rewrite IHi.
      change (S j' <? S i)%nat with (j' <? i)%nat. destruct (j' <? i)%nat; reflexivity.
Qed.

Lemma remove_nth_idx : forall i j1 j2, j1 <> j2 ->
  (if (j1 <? i)%nat then j1 else S j1) <> (if (j2 <? i)%nat then j2 else S j2)
  /\ (if (j1 <? i)%nat then j1 else S j1) <> i.
Proof.
  intros i j1 j2 NE. destruct (j1 <? i)%nat eqn:E1; destruct (j2 <? i)%nat eqn:E2;
    rewrite ?Nat.ltb_lt, ?Nat.ltb_ge in *; lia.
Qed.

Lemma structs_apart_remove : forall i ls, structs_apart ls -> structs_apart (remove_nth i ls).
Proof.
  intros i ls SA a b da db Ha Hb NE. rewrite nth_error_remove_nth in Ha, Hb.
  eapply SA; [exact Ha| exact Hb| exact (proj1 (remove_nth_idx i a b NE))].
Qed.
Lemma limbs_apart_remove : forall i ls, limbs_apart ls -> limbs_apart (remove_nth i ls).
Proof.
  intros i ls LA a b da db Ha Hb NE. rewrite nth_error_remove_nth in Ha, Hb.
  eapply LA; [exact Ha| exact Hb| exact (proj1 (remove_nth_idx i a b NE))].
Qed.
Lemma remove_nth_blk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pi,$0.Pls,(1.$2.)Pd,$2.Pb,$3.P,(4.(5.$2.)(6.$2.R3.R4.)(7.$2.R2.))P,(8.$3.R2.(9.$2.$3.$:.R4.))(;.(8.$3.R3.(:.R4.))(8.$3.R3.(9.$2.$3.$:.(<.$2.R6.R5.))))")
(* [comment removed for export] *).
Proof.
  induction i; intros [|x t] d b Hi Hb; cbn in *; try discriminate.
  - injection Hi as ->. apply in_app_iff in Hb. exact Hb.
  - apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [right; apply in_app_iff; left; exact Hb|].
    destruct (IHi t d b Hi Hb) as [K|K]; [left; exact K| right; apply in_app_iff; right; exact K].
Qed.
Lemma remove_nth_blk_in : forall i ls b, In b (flat_map mpd_blk (remove_nth i ls)) -> In b (flat_map mpd_blk ls).
Proof.
  intros i ls b Hb. apply in_flat_map in Hb. ddestruct Hb as (x & Hx & Hb). apply in_flat_map. exists x. split; [eapply In_remove_nth; exact Hx| exact Hb].
Qed.

(* [comment removed for export] *)
Lemma presA_drop_below_w : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Psegs,(1.$=.)PR,$>.PHIA,(?.R2.R1.)PLB,(1.(10.$11.$11.))PLF,(1.(10.$11.$11.))PW,(1.(10.$11.$11.))Pa,$11.Pb,$11.Pm1,P,(12.&40.)(5.(12.&8.))Pm2,P,(12.&40.)(5.(12.&8.))PSP,$11.PTOP,$11.P,Pbk,(10.$11.$11.)P,(8.(10.$11.$11.)R1.(13.(10.$11.$11.)R:.R9.))(14.(15.(16.$11.$11.R2.)(17.$11.$11.R2.))(18.(19.R=.)))P,(1:.R=.R<.R:.R9.R3.(1;.R<.)R2.(1<.(10.$11.$11.)(1=.$11.$11.R7.R6.)R8.)R5.R4.)P,(14.R7.R4.)P,(14.(1;.R>.)R9.)(1:.R10.R?.R=.R<.R6.(1;.R?.)R5.R;.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs R HIA LB LF W a b m1 m2 SP TOP HBR [P S] Hb Ha. split; [| exact S].
  pose proof (art_lo segs R HIA) as ALO. pose proof (art_data_lo segs R HIA) as DHI.
  intros x Hx Hc Ho. apply P; [exact Hx| exact Hc|]. cbn [outside]. split; [| exact Ho].
  intros Hin. destruct Hc as [Hs|[[Hd1 Hd2]|(bk & Hbk & Hr)]].
  - clear - Hs Hin Hb. lia.
  - clear - Hd1 Hin Ha ALO DHI. cbn in *. lia.
  - apply in_app_iff in Hbk. destruct Hbk as [Hbk|Hbk].
    + pose proof (HBR bk ltac:(apply in_app_iff; left; exact Hbk)) as HC. unfold alloc_ceiling in ALO. clear - HC Hr Hin Ha ALO. lia.
    + ddestruct (in_fdata_hull LF bk x Hbk Hr) as (fb & Hfb & Hr2).
      pose proof (HBR fb ltac:(apply in_app_iff; right; exact Hfb)) as HC. unfold alloc_ceiling in ALO. clear - HC Hr2 Hin Ha ALO. lia.
Qed.

Lemma In_mpd_keep_not_blk_w : forall LB d b, In b (mpd_keep LB d) -> ~ In b (mpd_blk d).
Proof.
  intros LB d b Hb. unfold mpd_keep in Hb. unfold mpd_blk. destruct (md_own d); [intros []| | intros []].
  apply filter_In in Hb. destruct Hb as [_ Hne]. intros [E|[]]. rewrite <- E in Hne.
  unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
Qed.

(* [comment removed for export] *)
Section MCA.
  Variable segs : list Segment.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA segs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis HND : forall h LB LF m, HM segs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.

  (* [comment removed for export] *)
  Variables (h0 : HST segs R HIA) (LB LF : list blk) (m0 : mem) (SP lo SPc FB FN : Z) (dW0 : mpd) (es : list mpd).
  Local Notation LF' := ((FB, FN) :: LF).
  Local Notation W0 := (md_addr dW0).
  Local Notation KEEP0 := (mpd_keep LB dW0).
  Hypothesis H0M : HM segs R HIA h0 LB LF m0.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis LOC : lo <= SPc.
  Hypothesis CSP : SPc <= SP.
  Hypothesis SPT : SP <= htop segs R HIA h0.
  Hypothesis FRSH : fresh_apart R LB LF FB FN.
  Hypothesis FN64 : 64 <= FN.
  Hypothesis FB8 : FB mod 8 = 0.
  Hypothesis W0NS : md_own dW0 <> LStatic.
  Hypothesis W0WR : mpd_writableA R LB LF SP (htop segs R HIA h0) dW0.
  Hypothesis W0AS : W0 + 16 <= lo \/ SP <= W0.
  Hypothesis W0BLK : md_own dW0 = LHeap -> In (md_p dW0, 4 * md_n dW0) LB /\ 1 <= md_n dW0.
  (* [comment removed for export] *)
  Hypothesis ESF : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "(1>.$2.Le,$2.(1?.(20.(19.VR,)(13.$3.VLB,(21.VLF,))Vlo,(22.R1.)+10.)(1?.P,(4.$23.(24.R1.)$25.)(1?.(8.(10.$11.$11.)(1=.$11.$11.(26.R2.)(27.+4.(28.R2.)))VLB,)(14.+1.(28.R2.)))(1?.(;.(14.(15.(22.R1.)+10.)Vlo,)(14.VSP,(22.R1.)))(1?.P,(4.$23.(24.VdW0,)$25.)(;.(14.(15.(22.R2.)+10.)(26.VdW0,))(14.(15.(26.VdW0,)(27.+4.(28.VdW0,)))(22.R2.)))(1?.(;.(29.(4.$23.(24.VdW0,)$25.))(;.(4.$23.(24.R1.)$2:.)(;.(14.(15.(26.VdW0,)(27.+4.(28.VdW0,)))(26.R1.))(14.(15.(26.R1.)(27.+4.(28.R1.)))(26.VdW0,)))))(1?.(;.(14.(15.(22.VdW0,)+10.)(22.R1.))(14.(15.(22.R1.)+10.)(22.VdW0,)))P,(29.(4.$23.(24.R1.)$2:.))(;.(14.(15.(22.VdW0,)+10.)(26.R2.))(14.(15.(26.R2.)(27.+4.(28.R2.)))(22.VdW0,)))))))))Ves,)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition struct_locA (A : Z) : Prop := (FB + 32 <= A /\ A + 16 <= FB + FN - 8) \/ (SPc <= A /\ A + 16 <= SP).

  Definition local_okA (mq : mem) (hq : HST segs R HIA) (LBq : list blk) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "(1?.(2;.Vsegs,O4.O2.O1.)(1?.(29.(4.$23.(24.O1.)$2<.))(1?.(2=.(22.O1.))(1?.(4.$11.(2>.(22.O1.)+8.)=)(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,O3.)O4.(22.O1.)+10.)))))")
(* [comment removed for export] *).

  Definition w_blk_okA (LBq : list blk) (ls : list mpd) (dW : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "(1?.(4.$11.(22.O1.)(22.VdW0,))(1?.(29.(4.$23.(24.O1.)$2<.))(1?.(1?.(4.(12.&40.)(32.O1.)(32.VdW0,))(14.(28.VdW0,)(28.O1.)))(1?.P,(4.$23.(24.O1.)$25.)(1?.(29.(8.(10.$11.$11.)(1=.$11.$11.(26.O1.)(27.+4.(28.O1.)))(9.$2.$3.$:.O2.)))(;.(8.(10.$11.$11.)(1=.$11.$11.(26.O1.)(27.+4.(28.O1.)))(:.VdW0,))(29.(8.(10.$11.$11.)(1=.$11.$11.(26.O1.)(27.+4.(28.O1.)))VLB,))))Pb,$3.P,(8.$3.R1.(:.VdW0,))P,(8.$3.R2.O3.)(;.(4.(1.$3.)(:.O1.)(:.VdW0,))(8.$3.R3.(9.$2.$3.$:.O2.)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition chunk_okA (ls : list mpd) (ac : Z * list cell) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "(1?.(;.(1?.(14.VSPc,(16.$11.(1.$33.)O1.))(14.(15.(16.$11.(1.$33.)O1.)(34.(35.(17.$11.(1.$33.)O1.))))VSP,))(;.(1?.(14.VFB,(16.$11.(1.$33.)O1.))(14.(15.(16.$11.(1.$33.)O1.)(34.(35.(17.$11.(1.$33.)O1.))))(15.VFB,+18.)))(1?.(14.(15.VFB,+20.)(16.$11.(1.$33.)O1.))(14.(15.(16.$11.(1.$33.)O1.)(34.(35.(17.$11.(1.$33.)O1.))))(36.(15.VFB,VFN,)+8.)))))Pd,$2.P,(8.$2.R1.O2.)(;.(14.(15.(16.$11.(1.$33.)O1.)(34.(35.(17.$11.(1.$33.)O1.))))(22.R2.))(14.(15.(22.R2.)+10.)(16.$11.(1.$33.)O1.))))")
(* [comment removed for export] *).

  Definition cstateA (mq : mem) (hq : HST segs R HIA) (LBq : list blk) (ls : list mpd) (dW : mpd)
      (CS : list (Z * list cell)) (SHC : list cell) (v f : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "(1?.(37.Vsegs,VR,VHIA,O8.O7.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)O9.)(1?.(1?.(4.$11.(38.Vsegs,VR,VHIA,O8.)(38.Vsegs,VR,VHIA,Vh0,))(1?.(4.$11.(39.Vsegs,VR,VHIA,O8.)(39.Vsegs,VR,VHIA,Vh0,))(4.$11.(3:.Vsegs,VR,VHIA,O8.)(3:.Vsegs,VR,VHIA,Vh0,))))(1?.Px,$11.P,(31.Vsegs,VR,VHIA,Vh0,R1.)(31.Vsegs,VR,VHIA,O8.R2.)(1?.(1?.(14.(3;.Vsegs,VR,VHIA,O8.)(15.(3;.Vsegs,VR,VHIA,Vh0,)O2.))(14.(3<.Vsegs,VR,VHIA,O8.)(15.(3<.Vsegs,VR,VHIA,Vh0,)O1.)))(1?.(1>.$2.(3=.O9.O8.O7.)O6.)(1?.(3>.O6.)(1?.(3?.O6.)(1?.(2;.Vsegs,O9.O7.O5.)(1?.(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,O8.)O9.(22.VdW0,)+10.)(1?.(40.O7.O6.O5.)(1?.Pb,$3.P,(8.$3.R1.VLB,)P,(29.(8.$3.R2.(:.VdW0,)))(8.$3.R3.O7.)(1?.Pb,$3.P,(8.$3.R1.O7.)(;.(8.$3.R2.VLB,)(;.(8.$3.R2.(9.$2.$3.$:.O6.))(8.$3.R2.(:.O5.))))(1?.Pb,$3.P,(8.$3.R1.(9.$2.$3.$:.O6.))P,(8.$3.R2.VLB,)(8.$3.R3.(:.VdW0,))(1?.(1>.$2.Le,$2.(1?.(2;.Vsegs,O9.O7.R1.)(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,O8.)O9.(22.R1.)+10.))Ves,)(1?.(1:.Vsegs,VR,(41.VLB,VdW0,)VLF,VSP,(1;.VR,)(39.Vsegs,VR,VHIA,Vh0,)(1<.(10.$11.$11.)(1=.$11.$11.(22.VdW0,)(15.(22.VdW0,)+10.))(42.(10.$11.$11.)))Vm0,O9.)(1?.Pb,$3.P,(8.$3.R1.(9.$2.$3.$:.O6.))(43.VR,(41.VLB,VdW0,)VLF,(16.$11.$11.R2.)(17.$11.$11.R2.))(1?.Pb,$3.P,(8.$3.R1.(:.O5.))(;.(8.$3.R2.(:.VdW0,))(43.VR,(41.VLB,VdW0,)VLF,(16.$11.$11.R2.)(17.$11.$11.R2.)))(1?.(44.Vsegs,O9.)(1?.(45.Vsegs,O9.Vlo,VSPc,)(1?.(1>.(10.$11.(1.$33.))Lac,(10.$11.(1.$33.))(46.Vsegs,O9.(16.$11.(1.$33.)R1.)(17.$11.(1.$33.)R1.))O4.)(1?.(1>.(10.$11.(1.$33.))(47.O6.)O4.)(1?.(46.Vsegs,O9.(15.(48.VFB,+3.)(49.(30.VR,)))O3.)(14.(27.+8.(34.(35.O3.)))VFN,)))))))))))))))))))))))")
(* [comment removed for export] *).

  Ltac dest_cs H :=
    destruct H as (HH & (HTc & HSc & HFc) & HCSc & (HVc & HFRc) & LOK & SA & LA & MW & OW & WOK & SUB & COV & FRS & EXT & PX & FRL & FRW & MI & ST & CH & CHS & SHD & SHN).

  (* [comment removed for export] *)
  #[using="segs HIA h0 LB LF SP SPc LOS LOC CSP FRSH FN64 W0WR"] Lemma mca_facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "(1?.(14.=Vlo,)(1?.(14.(4:.(19.VR,))(1;.VR,))(1?.(4;.=VFB,)(1?.(14.(15.VFB,VFN,)(4:.(19.VR,)))(;.(14.(15.VFB,VFN,)(22.VdW0,))(14.(15.(22.VdW0,)+10.)VFB,))))))")
(* [comment removed for export] *).
  Proof.
    pose proof (art_lo segs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP.
    ddestruct FRSH as (F0 & F1 & F2 & F3). destruct W0WR as [CW _].
    assert (CR : client_range L (LB ++ fdata LF) lo W0 16).
    { intros x Hx. destruct (CW x Hx) as [X|[X|X]]; [left; clear - X LOC CSP; lia| right; left; exact X| right; right; exact X]. }
    pose proof (fresh_apart_client R LB LF lo W0 16 FB FN FRSH CR ltac:(lia) ltac:(lia) ltac:(lia)) as AP.
    split; [lia|]. split; [exact ALO|]. split; [exact F0|]. split; [exact F1| exact AP].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma mpd_step : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Pm2,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)Ph2,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)PLBk,(1.$3.)PLB2,(1.$3.)PSPx,$11.PWX,(1.$4=.)Pd,$2.P,(2;.Vsegs,R:.R6.R1.)P,(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,R9.)R;.(22.R2.)+10.)P,(1:.Vsegs,VR,R7.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R5.(1;.VR,)(39.Vsegs,VR,VHIA,R:.)R4.R<.R;.)P,(44.Vsegs,R=.)P,(44.Vsegs,R=.)P,Px,$11.P,(31.Vsegs,VR,VHIA,R>.R1.)(31.Vsegs,VR,VHIA,R>.R2.)P,(14.(1;.VR,)R9.)P,(20.(19.VR,)(13.$3.R<.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))R:.(22.R8.)+10.)P,P,(4.$23.(24.R9.)$25.)(8.(10.$11.$11.)(1=.$11.$11.(26.R:.)(27.+4.(28.R:.)))R>.)P,(4>.R;.(22.R:.)+10.)P,P,(4.$23.(24.R;.)$25.)(4>.R=.(26.R<.)(27.+4.(28.R<.)))P,Pb,$3.P,(8.$3.R1.(:.R=.))(8.$3.R2.R11.)(1?.(2;.Vsegs,R15.R10.R=.)(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,R13.)R15.(22.R=.)+10.))")
(* [comment removed for export] *).
  Proof.
    intros mq m2 hq h2 LBq LBk LB2 SPx WX d MD OD HP MI MI2 HCS2 HSX CR INL D1 D2 HBL. split.
    - eapply (mpd_at_heap_presx segs L) with (LBp := LBk ++ fdata LF') (SP := SPx) (XI := WX);
        [exact MD| exact (presA_presx segs R _ _ _ _ _ _ _ _ HP)| exact MI| exact MI2| exact CR| | exact D1| exact D2| exact HBL].
      intros EO. pose proof MD as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. destruct OW as (N1 & _).
      eapply client_range_block; [apply in_app_iff; left; exact (INL EO)| clear; lia| clear; lia].
    - eapply aobj_cs_mono; [exact HCS2|].
      eapply (presA_aobj segs R); [exact (hcs_ok segs R HIA hq)| exact HP| exact OD| exact CR| exact HSX| intros x Hx; eapply hcs_below_top; exact Hx].
  Qed.

  (* [comment removed for export] *)
  #[using="FN64"] Lemma frame_client : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "PLBk,(1.$3.)PSPx,$11.PA,$11.Pn,$11.P,(;.(1?.(14.VFB,R2.)(14.(15.R2.R1.)(15.VFB,+18.)))(1?.(14.(15.VFB,+20.)R2.)(14.(15.R2.R1.)(36.(15.VFB,VFN,)+8.))))(20.(19.VR,)(13.$3.R5.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))R4.R3.R2.)")
(* [comment removed for export] *).
  Proof.
    intros LBk SPx A n [[H1 H2]|[H1 H2]].
    - eapply client_range_block; [apply in_app_iff; right; cbn [fdata]; left; reflexivity| exact H1| clear - H2 FN64; lia].
    - eapply client_range_block; [apply in_app_iff; right; cbn [fdata]; right; left; reflexivity| exact H1| clear - H2; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="FN64"] Lemma loc_client : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "PLBk,(1.$3.)PSPx,$11.PA,$11.P,(2=.R1.)P,P,(14.VSPc,R2.)(14.R4.R3.)(20.(19.VR,)(13.$3.R5.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))R4.R3.+10.)")
(* [comment removed for export] *).
  Proof.
    intros LBk SPx A [[H1 H2]|[H1 H2]] HS.
    - apply frame_client. right. split; [exact H1| exact H2].
    - apply client_range_stack. exact (HS H1).
  Qed.

  #[using="Type"] Lemma loc_wclient : forall LBk TOP A, struct_locA A -> SP <= TOP -> client_wrange L (LBk ++ fdata LF') SPc TOP A 16.
  Proof.
    intros LBk TOP A [[H1 H2]|[H1 H2]] HT.
    - eapply client_wrange_block; [apply in_app_iff; right; cbn [fdata]; right; left; reflexivity| exact H1| clear - H2; lia].
    - apply client_wrange_stack; [exact H1| clear - H2 HT; lia].
  Qed.

  #[using="segs R HIA h0 LB LF dW0 LOS LOC CSP FRSH FN64 W0WR"] Lemma loc_lo : forall A, struct_locA A -> A + 16 <= lo \/ SPc <= A.
  Proof.
    intros A [[H1 H2]|[H1 H2]]; [left| right; exact H1].
    dpose (mca_facts) as (LO0 & ALO & F0 & F1 & _). clear - H2 F1 ALO LOS. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="segs HIA h0 LB LF lo dW0 LOS LOC CSP FRSH FN64 W0WR"] Lemma loc_vs_low : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "PA,$11.PB,$11.Pk,$11.P,(2=.R3.)P,(14.(15.R3.R2.)(4:.(19.VR,)))P,(;.(14.(15.R4.R3.)VFB,)(14.(15.VFB,VFN,)R4.))(;.(14.(15.R5.R4.)R6.)(14.(15.R6.+10.)R5.))")
(* [comment removed for export] *).
  Proof.
    intros A B k [[H1 H2]|[H1 H2]] HC HF; [clear - H1 H2 HF FN64; lia|].
    dpose (mca_facts) as (LO0 & ALO & F0 & F1 & _). left. clear - H1 HC ALO LOS LOC. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="segs R HIA h0 LB LF lo LOS LOC CSP FRSH FN64 W0WR W0AS"] Lemma loc_vs_w : forall A, struct_locA A -> A + 16 <= W0 \/ W0 + 16 <= A.
  Proof.
    intros A [[H1 H2]|[H1 H2]]; dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    - clear - H1 H2 WFB FN64. lia.
    - clear - H1 H2 W0AS LOC. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="h0 LB lo dW0 es LOS LOC CSP FRSH FN64 W0WR ESF"] Lemma cells_step : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Pm2,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBk,(1.$3.)PSPx,$11.PWX,(1.$4=.)Pls,(1.$2.)PCS,(1.(10.$11.(1.$33.)))P,(1:.Vsegs,VR,R5.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R4.(1;.VR,)(39.Vsegs,VR,VHIA,R6.)R3.R8.R7.)P,(1>.(10.$11.(1.$33.))Lac,(10.$11.(1.$33.))(46.Vsegs,R:.(16.$11.(1.$33.)R1.)(17.$11.(1.$33.)R1.))R2.)P,(1>.(10.$11.(1.$33.))(47.R4.)R3.)P,(1>.(10.$11.(1.$33.))Lac,(10.$11.(1.$33.))(1?.(;.(14.R8.(16.$11.(1.$33.)R1.))(4;.(16.$11.(1.$33.)R1.)(15.VFB,VFN,)))(4>.R7.(16.$11.(1.$33.)R1.)(34.(35.(17.$11.(1.$33.)R1.)))))R4.)(1>.(10.$11.(1.$33.))Lac,(10.$11.(1.$33.))(46.Vsegs,R<.(16.$11.(1.$33.)R1.)(17.$11.(1.$33.)R1.))R5.)")
(* [comment removed for export] *).
  Proof.
    intros mq m2 hq LBk SPx WX ls CS HP CH CHS CHX. rewrite Forall_forall in *. intros ac Hac.
    destruct (CHX ac Hac) as [POS DJ]. dpose (mca_facts) as (LO0 & ALO & F0 & F1 & _).
    eapply (presA_rw_cells segs R); [exact HP| exact (CH ac Hac)| | exact DJ].
    ddestruct (CHS ac Hac) as [[[C1 C2]|[C|[C1 C2]]] _].
    - apply client_range_stack. destruct POS as [P|P]; [exact P| exfalso; clear - P C1 F1 ALO LOS LOC; lia].
    - apply frame_client. left. exact C.
    - apply frame_client. right. split; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="h0 LB SP lo SPc dW0 LOS LOC CSP FRSH FN64 FB8 W0WR"] Lemma shadow_step : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Pm2,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBk,(1.$3.)PSPx,$11.PWX,(1.$4=.)PSHC,(1.$33.)P,(;.(37.Vsegs,VR,VHIA,R5.R4.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R7.)Px,$11.P,(1?.(14.VFB,R1.)(4;.R1.(15.VFB,VFN,)))(31.Vsegs,VR,VHIA,R7.R2.))P,(1:.Vsegs,VR,R5.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R4.(1;.VR,)(39.Vsegs,VR,VHIA,R6.)R3.R8.R7.)P,(46.Vsegs,R9.(15.(48.VFB,+3.)(49.(30.VR,)))R3.)P,(14.(27.+8.(34.(35.R4.)))VFN,)(46.Vsegs,R:.(15.(48.VFB,+3.)(49.(30.VR,)))R5.)")
(* [comment removed for export] *).
  Proof.
    intros mq m2 hq LBk SPx WX SHC HF HP SHD SHN. dpose (mca_facts) as (LO0 & ALO & F0 & F1 & _).
    eapply (presA_shadow_cells_sh segs R (hcs segs R HIA hq)); [exact (hcs_ok segs R HIA hq)| | exact FB8| clear - F0; lia| exact HP| exact SHD|].
    - intros x Hx. destruct HF as [HH|HF]; [| apply HF; clear - Hx SHN; lia].
      replace x with (FB + (x - FB)) by (clear; lia). eapply (hcs_fake segs R HIA hq _ _ mq FB FN HH); [left; reflexivity| clear - Hx SHN; lia].
    - intros c Hc. right; right; left. exists (FB, FN). split; [left; reflexivity| cbn [fst snd]; clear - Hc SHN; lia].
  Qed.

  #[using="R DIMG SP lo dW0 W0AS"] Lemma outside_app_w : forall (l1 l2 : list ivl) a, outside (l1 ++ l2) a <-> outside l1 a /\ outside l2 a.
  Proof. induction l1 as [|[c d] l1 IH]; intros l2 a; cbn; [tauto|]. rewrite IH. tauto. Qed.

  (* [comment removed for export] *)
  Definition wx_ok (w : ivl) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "(;.(4.$4=.O1.(1=.$11.$11.(22.VdW0,)(15.(22.VdW0,)+10.)))(;.(1?.(14.VFB,(16.$11.$11.O1.))(14.(17.$11.$11.O1.)(15.VFB,VFN,)))(;.(43.VR,(41.VLB,VdW0,)VLF,(16.$11.$11.O1.)(36.(17.$11.$11.O1.)(16.$11.$11.O1.)))(1?.(14.(1;.VR,)(16.$11.$11.O1.))(14.(17.$11.$11.O1.)VSP,)))))")
(* [comment removed for export] *).

  #[using="DIMG lo SPc H0M LOS LOC CSP FRSH FN64 W0WR W0AS"] Lemma pres_step : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Pm2,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBk,(1.$3.)PSPx,$11.PWX,(1.$4=.)P,(1:.Vsegs,VR,(41.VLB,VdW0,)VLF,VSP,(1;.VR,)(39.Vsegs,VR,VHIA,Vh0,)(1<.(10.$11.$11.)(1=.$11.$11.(22.VdW0,)(15.(22.VdW0,)+10.))(42.(10.$11.$11.)))Vm0,R6.)P,(1:.Vsegs,VR,R4.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R3.(1;.VR,)(39.Vsegs,VR,VHIA,R5.)R2.R7.R6.)P,(4.$11.(39.Vsegs,VR,VHIA,R6.)(39.Vsegs,VR,VHIA,Vh0,))P,Pb,$3.P,(8.$3.R1.(41.VLB,VdW0,))(8.$3.R2.R8.)P,(14.R6.VSP,)P,(1>.$4=.$4?.R6.)(1:.Vsegs,VR,(41.VLB,VdW0,)VLF,VSP,(1;.VR,)(39.Vsegs,VR,VHIA,Vh0,)(1<.(10.$11.$11.)(1=.$11.$11.(22.VdW0,)(15.(22.VdW0,)+10.))(42.(10.$11.$11.)))Vm0,R;.)")
(* [comment removed for export] *).
  Proof.
    intros mq m2 hq LBk SPx WX PX HP HS SUBK HSX HWX. dpose (mca_facts) as (LO0 & ALO & F0 & F1 & _).
    eapply presA_trans; [exact PX|]. rewrite HS in HP.
    assert (G : forall WX', Forall wx_ok WX' ->
                presA segs R KEEP0 LF SP (arl_stklo R) (hstkhi segs R HIA h0) (WX' ++ [(W0, W0 + 16)]) mq m2 ->
                presA segs R KEEP0 LF SP (arl_stklo R) (hstkhi segs R HIA h0) [(W0, W0 + 16)] mq m2).
    { induction WX' as [|w WX' IH]; intros HF HPx; [exact HPx|]. inversion HF as [|w' l' Hw HF']; subst w' l'. apply IH; [exact HF'|].
      cbn [app] in HPx. destruct Hw as [E|[[A1 A2]|[FR|[S1 S2]]]].
      - subst w. eapply presA_weaken; [exact HPx| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside]. split; [| exact Hx]. apply outside_app_w in Hx. destruct Hx as [_ Hx]. cbn [outside] in Hx. exact (proj1 Hx).
      - destruct w as [a b]. cbn [fst snd] in A1, A2. destruct HPx as [P S]. split; [| exact S].
        dpose (fresh_apart_keep R LB LF dW0 FB FN FRSH) as (G0 & G1 & G2 & G3).
        intros x Hx Hc Ho. apply P; [exact Hx| exact Hc|]. cbn [outside]. split; [| exact Ho].
        intros Hin. destruct Hc as [Hs|[[Hd1 Hd2]|(bk & Hbk & Hr)]].
        + clear - Hs Hin G1 A1 A2 ALO LOS LOC CSP. lia.
        + clear - Hd1 Hd2 Hin G2 A1 A2. cbn in *. lia.
        + destruct bk as [B j]. cbn in Hr. pose proof (G3 B j Hbk) as K. clear - Hr Hin K A1 A2. lia.
      - destruct w as [a b]. cbn [fst snd] in FR.
        eapply (presA_drop_fresh segs R HIA h0 KEEP0 LF _ a (b - a) mq m2 SP); [| exact FR| clear - LOS LOC CSP; lia].
        replace (a + (b - a)) with b by (clear; lia). exact HPx.
      - destruct w as [a b]. cbn [fst snd] in S1, S2.
        eapply (presA_drop_below_w segs R HIA KEEP0 LF _ a b mq m2 SP); [| exact HPx| exact S2| exact S1].
        intros bk Hbk. destruct (hm_apart segs R HIA h0 LB LF m0 H0M) as [HBR _]. rewrite Forall_forall in HBR.
        assert (Hb' : In bk (LB ++ LF)) by (apply in_app_iff in Hbk; apply in_app_iff; destruct Hbk as [K|K]; [left; eapply In_mpd_keep; exact K| right; exact K]).
        ddestruct (HBR bk Hb') as (_ & _ & HC & _). exact HC. }
    apply (G WX HWX).
    eapply presA_weaken; [exact HP| exact SUBK| intros b Hb; right; exact Hb| exact HSX| clear; lia| clear; lia|].
    intros x Hx. apply outside_app_w in Hx. exact (proj1 Hx).
  Qed.

  (* [comment removed for export] *)
  #[using="lo LOS LOC"] Lemma loc_wx : forall A, struct_locA A -> wx_ok (A, A + 16).
  Proof.
    intros A [[H1 H2]|[H1 H2]]; unfold wx_ok; cbn [fst snd].
    - right; left. clear - H1 H2. lia.
    - right; right; right. clear - H1 H2 LOS LOC. lia.
  Qed.

  #[using="Type"] Lemma blocks_apart_app2_w : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "PL1,(1.$3.)PL2,(1.$3.)Pb1,$3.Pb2,$3.P,(50.(13.$3.R4.R3.))P,(8.$3.R3.R5.)P,(8.$3.R3.R5.)(;.(14.(15.(16.$11.$11.R5.)(17.$11.$11.R5.))(16.$11.$11.R4.))(14.(15.(16.$11.$11.R4.)(17.$11.$11.R4.))(16.$11.$11.R5.)))")
(* [comment removed for export] *).
  Proof.
    induction L1 as [|[x y] L1 IH]; cbn; intros L2 b1 b2 H H1 H2; [destruct H1|].
    destruct H as [Hx H]. destruct H1 as [<-|H1].
    - cbn. destruct b2 as [B k]. cbn. apply Hx. apply in_app_iff. right. exact H2.
    - eapply IH; eauto.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma blk_facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)PB,$11.Pk,$11.P,(37.Vsegs,VR,VHIA,R4.R3.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R5.)P,(8.(10.$11.$11.)(1=.$11.$11.R3.R2.)R4.)(1?.(4;.=R4.)(1?.(14.(15.R4.R3.)(4:.(19.VR,)))(;.(14.(15.R4.R3.)VFB,)(14.(15.VFB,VFN,)R4.))))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq B k HH Hb. destruct (hm_apart segs R HIA hq LBq LF' mq HH) as [HBR BA]. rewrite Forall_forall in HBR.
    ddestruct (HBR (B, k) ltac:(apply in_app_iff; left; exact Hb)) as (B0 & _ & BC & _). cbn [fst snd] in B0, BC.
    split; [exact B0|]. split; [exact BC|].
    pose proof (blocks_apart_app2_w LBq LF' (B, k) (FB, FN) BA Hb ltac:(left; reflexivity)) as K. cbn [fst snd] in K. exact K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="LOS LOC CSP SPT FRSH FN64 W0WR"] Lemma cs_local_facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pi,$0.Pd,$2.P,(51.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4.(5.$2.)(6.$2.R9.R3.)(7.$2.R2.))(1?.(2;.Vsegs,R=.R;.R3.)(1?.(29.(4.$23.(24.R3.)$2<.))(1?.(52.VR,R;.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)VSPc,(38.Vsegs,VR,VHIA,R<.)R3.)(1?.P,(29.(4.$23.(24.R3.)$2:.))(;.(14.(15.(26.R4.)(27.+4.(28.R4.)))Vlo,)(14.VSPc,(26.R4.)))(1?.(20.(19.VR,)(13.$3.R;.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))Vlo,(22.R3.)+10.)(1?.P,(4.$23.(24.R3.)$25.)(20.(19.VR,)(13.$3.R<.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))Vlo,(26.R4.)(27.+4.(28.R4.)))(1?.P,(4.$23.(24.R3.)$25.)(1?.(4;.=(26.R4.))(1?.(14.(15.(26.R4.)(27.+4.(28.R4.)))(4:.(19.VR,)))(1?.(8.(10.$11.$11.)(1=.$11.$11.(26.R4.)(27.+4.(28.R4.)))R<.)(1?.(14.+1.(28.R4.))(1?.(;.(14.(15.(26.R4.)(27.+4.(28.R4.)))VFB,)(14.(15.VFB,VFN,)(26.R4.)))(43.VR,(41.VLB,VdW0,)VLF,(26.R4.)(27.+4.(28.R4.))))))))(1?.(2=.(22.R3.))(1?.(4.$11.(2>.(22.R3.)+8.)=)(1?.(;.(14.(15.(22.R3.)+10.)Vlo,)(14.VSPc,(22.R3.)))(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,R<.)R=.(22.R3.)+10.)))))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f i d CST Hi. dest_cs CST. dpose (mca_facts) as (LO0 & ALO & F0 & F1 & _).
    pose proof (proj1 (Forall_forall _ _) LOK d (nth_error_In _ _ Hi)) as (MD & NS & DL & D8 & OD).
    assert (HF : md_own d = LHeap -> 0 < md_p d /\ md_p d + 4 * md_n d <= alloc_ceiling /\ In (md_p d, 4 * md_n d) LBq /\ 1 <= md_n d
                   /\ (md_p d + 4 * md_n d <= FB \/ FB + FN <= md_p d) /\ fresh_apart R KEEP0 LF (md_p d) (4 * md_n d)).
    { intros O. pose proof MD as [(_ & _ & _ & _ & _ & OWNd) _]. rewrite O in OWNd. ddestruct OWNd as (N1 & IN & _).
      destruct (blk_facts _ _ _ _ _ HH IN) as (B0 & BC & BF).
      split; [exact B0|]. split; [exact BC|]. split; [exact IN|]. split; [exact N1|]. split; [exact BF|].
      apply (FRL (md_p d, 4 * md_n d)). apply in_flat_map. exists d. split; [eapply nth_error_In; exact Hi| apply mpd_blk_in; exact O]. }
    split; [exact MD|]. split; [exact NS|].
    split.
    { split.
      - apply loc_wclient; [exact DL| rewrite HTc; exact SPT].
      - intros O. ddestruct (HF O) as (_ & BC & _ & N1 & BF & _). destruct (loc_vs_low _ _ _ DL BC BF) as [K|K]; [right; exact K| left; exact K]. }
    split. { intros NN. left. destruct (md_own d) eqn:O; [exfalso; exact (NN eq_refl)| | exfalso; exact (NS eq_refl)].
             ddestruct (HF eq_refl) as (_ & BC & _). clear - BC ALO LOS. lia. }
    split. { apply loc_client; [exact DL| intros K; clear - K LOC; lia]. }
    split. { intros O. ddestruct (HF O) as (_ & _ & IN & N1 & _). eapply client_range_block; [apply in_app_iff; left; exact IN| clear; lia| clear; lia]. }
    split; [exact HF|]. split; [exact DL|]. split; [exact D8|]. split; [exact (loc_lo _ DL)| exact OD].
  Qed.

  (* [comment removed for export] *)
  #[using="segs HIA h0 SP SPc LOC CSP W0WR"] Lemma w0_client : client_range L (KEEP0 ++ fdata LF) lo W0 16.
  Proof.
    pose proof (mpd_writableA_keep R LB LF _ _ dW0 W0WR) as CW.
    intros x Hx. destruct (CW x Hx) as [X|[X|X]]; [left; clear - X LOC CSP; lia| right; left; exact X| right; right; exact X].
  Qed.

  #[using="LOS LOC CSP FRSH FN64 W0WR W0AS"] Lemma cs_w_facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.P,(51.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(1?.(2;.Vsegs,R:.R8.R6.)(1?.(29.(4.$23.(24.R6.)$2<.))(1?.(4.$11.(22.R6.)(22.VdW0,))(1?.(52.VR,R8.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)VSPc,(38.Vsegs,VR,VHIA,R9.)R6.)(1?.P,(29.(4.$23.(24.R6.)$2:.))(;.(14.(15.(26.R7.)(27.+4.(28.R7.)))Vlo,)(14.VSPc,(26.R7.)))(1?.(20.(19.VR,)(13.$3.R8.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))Vlo,(22.VdW0,)+10.)(1?.P,(4.$23.(24.R6.)$25.)(20.(19.VR,)(13.$3.R9.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))Vlo,(26.R7.)(27.+4.(28.R7.)))(1?.P,(4.$23.(24.R6.)$25.)(1?.(4;.=(26.R7.))(1?.(14.(15.(26.R7.)(27.+4.(28.R7.)))(4:.(19.VR,)))(1?.(8.(10.$11.$11.)(1=.$11.$11.(26.R7.)(27.+4.(28.R7.)))R9.)(1?.(14.+1.(28.R7.))(1?.(;.(14.(15.(26.R7.)(27.+4.(28.R7.)))VFB,)(14.(15.VFB,VFN,)(26.R7.)))(;.(14.(15.(22.VdW0,)+10.)(26.R7.))(14.(15.(26.R7.)(27.+4.(28.R7.)))(22.VdW0,))))))))(1?.(;.(14.(15.(22.VdW0,)+10.)Vlo,)(14.VSP,(22.VdW0,)))(1?.(;.(14.(15.VFB,VFN,)(22.VdW0,))(14.(15.(22.VdW0,)+10.)VFB,))(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,R9.)R:.(22.VdW0,)+10.)))))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f CST. dest_cs CST. dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    ddestruct WOK as (EA & NSW & _ & _ & _).
    assert (KSUB : forall b, In b (KEEP0 ++ fdata LF) -> In b (LBq ++ fdata LF')).
    { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; cbn [fdata]; right; right; exact Hb].
      apply SUB; [eapply In_mpd_keep; exact Hb| exact (In_mpd_keep_not_blk_w _ _ _ Hb)]. }
    assert (HF : md_own dW = LHeap -> 0 < md_p dW /\ md_p dW + 4 * md_n dW <= alloc_ceiling /\ In (md_p dW, 4 * md_n dW) LBq /\ 1 <= md_n dW
                   /\ (md_p dW + 4 * md_n dW <= FB \/ FB + FN <= md_p dW) /\ (W0 + 16 <= md_p dW \/ md_p dW + 4 * md_n dW <= W0)).
    { intros O. pose proof MW as [(_ & _ & _ & _ & _ & OWN) _]. rewrite O in OWN. ddestruct OWN as (N1 & IN & _).
      destruct (blk_facts _ _ _ _ _ HH IN) as (B0 & BC & BF). repeat (split; [assumption|]).
      destruct (FRW (md_p dW, 4 * md_n dW) ltac:(apply mpd_blk_in; exact O)) as [K|K].
      - destruct (mpd_blk_heap _ _ K) as [O0 E]. injection E as E1 E2. destruct W0WR as [_ AP]. specialize (AP O0). rewrite E1. clear - AP E2. lia.
      - cbn [fst snd] in K.
        pose proof (fresh_apart_client R KEEP0 LF lo W0 16 (md_p dW) (4 * md_n dW) K w0_client ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as AP.
        clear - AP. lia. }
    assert (CW : client_wrange L (LBq ++ fdata LF') SPc (htop segs R HIA hq) W0 16).
    { rewrite HTc. eapply client_wrange_sp_mono; [exact CSP|].
      eapply client_wrange_mono; [exact (mpd_writableA_keep R LB LF _ _ dW0 W0WR)| exact KSUB]. }
    split; [exact MW|]. split; [exact NSW|]. split; [exact EA|].
    split. { split; [rewrite EA; exact CW|]. intros O. rewrite EA. ddestruct (HF O) as (_ & _ & _ & _ & _ & AP). exact AP. }
    split. { intros NN. left. destruct (md_own dW) eqn:O; [exfalso; exact (NN eq_refl)| | exfalso; exact (NSW eq_refl)].
             ddestruct (HF eq_refl) as (_ & BC & _). clear - BC ALO LOS. lia. }
    split. { intros x Hx. destruct (w0_client x Hx) as [X|[X|(b & Hb & Rb)]]; [left; exact X| right; left; exact X| right; right; exists b; split; [exact (KSUB b Hb)| exact Rb]]. }
    split. { intros O. ddestruct (HF O) as (_ & _ & IN & N1 & _). eapply client_range_block; [apply in_app_iff; left; exact IN| clear; lia| clear; lia]. }
    split; [exact HF|]. split; [exact W0AS|]. split; [exact WFB| exact OW].
  Qed.

  #[using="LOS LOC CSP FRSH FN64 W0WR ESF"] Lemma cs_ext_facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pe,$2.P,(51.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(8.$2.R2.Ves,)(1?.(2;.Vsegs,R<.R:.R3.)(1?.(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,R;.)R<.(22.R3.)+10.)(1?.(20.(19.VR,)(13.$3.R:.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))Vlo,(22.R3.)+10.)(1?.P,(4.$23.(24.R3.)$25.)(20.(19.VR,)(13.$3.R;.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))Vlo,(26.R4.)(27.+4.(28.R4.)))(1?.P,(4.$23.(24.R3.)$25.)(1?.(8.(10.$11.$11.)(1=.$11.$11.(26.R4.)(27.+4.(28.R4.)))R;.)(1?.(8.(10.$11.$11.)(1=.$11.$11.(26.R4.)(27.+4.(28.R4.)))(41.VLB,VdW0,))(14.+1.(28.R4.))))(1?.(;.(14.(15.(22.R3.)+10.)Vlo,)(14.VSP,(22.R3.)))(;.(14.(15.VFB,VFN,)(22.R3.))(14.(15.(22.R3.)+10.)VFB,))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f e CST He. dest_cs CST. dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    pose proof (proj1 (Forall_forall _ _) EXT e He) as [ME OE].
    pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE & INE & ASE & E4 & E5 & E6 & E7).
    assert (KE : md_own e = LHeap -> In (md_p e, 4 * md_n e) KEEP0).
    { intros O. destruct (INE O) as [IN N1]. apply In_mpd_keep_intro; [exact IN|]. intros K.
      destruct (mpd_blk_heap _ _ K) as [O0 E]. injection E as E1 E2.
      destruct E5 as [C|[C|C]]; [exact (C O0)| rewrite O in C; discriminate C| clear - C E1 E2 N1; lia]. }
    split; [exact ME|]. split; [exact OE|].
    split.
    { intros x Hx. destruct (CRE x Hx) as [X|[X|(b & Hb & Rb)]]; [left; exact X| right; left; exact X| right; right; exists b; split; [| exact Rb]].
      apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; cbn [fdata]; right; right; exact Hb].
      apply SUB; [exact Hb|]. intros K. destruct (mpd_blk_heap _ _ K) as [O0 E]. subst b. cbn [fst snd] in Rb.
      specialize (E4 O0). clear - E4 Rb Hx. lia. }
    split. { intros O. destruct (INE O) as [IN N1]. eapply client_range_block; [apply in_app_iff; left; apply SUB; [exact IN| exact (In_mpd_keep_not_blk_w _ _ _ (KE O))]| clear; lia| clear; lia]. }
    split. { intros O. destruct (INE O) as [IN N1]. split; [apply SUB; [exact IN| exact (In_mpd_keep_not_blk_w _ _ _ (KE O))]| split; [exact (KE O)| exact N1]]. }
    split; [exact ASE|].
    exact (fresh_apart_client R LB LF lo (md_addr e) 16 FB FN FRSH CRE ltac:(clear; lia) ltac:(clear - FN64; lia) ltac:(clear - ALO LOS; lia)).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma cs_set_cells : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.PCS',(1.(10.$11.(1.$33.)))P,(51.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(1>.(10.$11.(1.$33.))Lac,(10.$11.(1.$33.))(46.Vsegs,R<.(16.$11.(1.$33.)R1.)(17.$11.(1.$33.)R1.))R2.)P,(1>.(10.$11.(1.$33.))(47.R9.)R3.)(51.R=.R<.R;.R:.R9.R4.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f CS' CST C1 C2. dest_cs CST. unfold cstateA.
    split; [exact HH|]. split; [exact (conj HTc (conj HSc HFc))|]. split; [exact HCSc|]. split; [exact (conj HVc HFRc)|].
    repeat (split; [assumption|]). assumption.
  Qed.

  #[using="Type"] Lemma cs_cells : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.P,(51.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(1?.(1>.(10.$11.(1.$33.))Lac,(10.$11.(1.$33.))(46.Vsegs,R;.(16.$11.(1.$33.)R1.)(17.$11.(1.$33.)R1.))R5.)(1?.(46.Vsegs,R:.(15.(48.VFB,+3.)(49.(30.VR,)))R4.)(1?.(44.Vsegs,R:.)(1?.(45.Vsegs,R:.Vlo,VSPc,)(37.Vsegs,VR,VHIA,R9.R8.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R:.)))))")
(* [comment removed for export] *).
  Proof. intros mq hq LBq ls dW CS SHC v f CST. dest_cs CST. repeat (split; [assumption|]). assumption. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma cs_budget : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.P,(51.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(1?.(4.$11.(38.Vsegs,VR,VHIA,R9.)(38.Vsegs,VR,VHIA,Vh0,))(1?.(4.$11.(39.Vsegs,VR,VHIA,R9.)(39.Vsegs,VR,VHIA,Vh0,))(1?.(4.$11.(3:.Vsegs,VR,VHIA,R9.)(3:.Vsegs,VR,VHIA,Vh0,))(1?.Px,$11.P,(31.Vsegs,VR,VHIA,Vh0,R1.)(31.Vsegs,VR,VHIA,R;.R2.)(1?.(14.(3;.Vsegs,VR,VHIA,R9.)(15.(3;.Vsegs,VR,VHIA,Vh0,)R3.))(14.(3<.Vsegs,VR,VHIA,R9.)(15.(3<.Vsegs,VR,VHIA,Vh0,)R2.)))))))")
(* [comment removed for export] *).
  Proof. intros mq hq LBq ls dW CS SHC v f CST. dest_cs CST. repeat (split; [assumption|]). assumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma cs_final : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.P,(51.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,(1>.$2.Ld,$2.(4.$23.(24.R1.)$2:.)R7.)(1?.(37.Vsegs,VR,VHIA,R:.R9.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R;.)(1?.(4.$11.(38.Vsegs,VR,VHIA,R:.)(38.Vsegs,VR,VHIA,Vh0,))(1?.(4.$11.(39.Vsegs,VR,VHIA,R:.)(39.Vsegs,VR,VHIA,Vh0,))(1?.(4.$11.(3:.Vsegs,VR,VHIA,R:.)(3:.Vsegs,VR,VHIA,Vh0,))(1?.Px,$11.P,(31.Vsegs,VR,VHIA,Vh0,R1.)(31.Vsegs,VR,VHIA,R<.R2.)(1?.(14.(3;.Vsegs,VR,VHIA,R:.)(15.(3;.Vsegs,VR,VHIA,Vh0,)R4.))(1?.(14.(3<.Vsegs,VR,VHIA,R:.)(15.(3<.Vsegs,VR,VHIA,Vh0,)R3.))(1?.(2;.Vsegs,R;.R9.R7.)(1?.(53.VLB,VdW0,R9.R7.)(1?.(54.VLB,VdW0,R7.)(1?.Pb,$3.P,(8.$3.R1.(:.R8.))(;.(8.$3.R2.(:.VdW0,))(43.VR,(41.VLB,VdW0,)VLF,(16.$11.$11.R2.)(17.$11.$11.R2.)))(1?.(1:.Vsegs,VR,(41.VLB,VdW0,)VLF,VSP,(1;.VR,)(39.Vsegs,VR,VHIA,Vh0,)(1<.(10.$11.$11.)(1=.$11.$11.(22.VdW0,)(15.(22.VdW0,)+10.))(42.(10.$11.$11.)))Vm0,R;.)(1?.(44.Vsegs,R;.)(1?.(45.Vsegs,R;.Vlo,VSPc,)(1?.(1>.(10.$11.(1.$33.))Lac,(10.$11.(1.$33.))(46.Vsegs,R<.(16.$11.(1.$33.)R1.)(17.$11.(1.$33.)R1.))R6.)(46.Vsegs,R;.(15.(48.VFB,+3.)(49.(30.VR,)))R5.))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f CST NUL. dest_cs CST. ddestruct WOK as (X1 & X2 & [X3 X4] & WB & WK).
    assert (NOBLK : forall b, ~ In b (flat_map mpd_blk ls)).
    { intros b Hb. apply in_flat_map in Hb. ddestruct Hb as (d & Hd & Hb). pose proof (proj1 (Forall_forall _ _) NUL d Hd) as O. cbn in O. unfold mpd_blk in Hb. rewrite O in Hb. exact Hb. }
    split; [exact HH|]. split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HCSc|]. split; [exact HVc|]. split; [exact HFRc|].
    split; [exact MW|].
    split.
    { split; [exact X1|]. split; [exact X2|]. split.
      - intros b Hb. destruct (COV b Hb) as [X|[X|X]]; [left; exact X| destruct (NOBLK _ X)| right; exact X].
      - split; [exact SUB|]. intros b Hb0 Hbq. destruct (WK b Hb0 Hbq) as [X|X]; [exact X| destruct (NOBLK _ X)]. }
    split.
    { split; [exact X1|]. split; [exact X3|]. split; [| exact X4].
      intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. destruct (proj2 (WB O)) as [Y|N]; [left; exact Y| right; exact N]. }
    split; [exact FRW|]. split; [exact PX|]. split; [exact MI|]. split; [exact ST|]. split; [exact CH| exact SHD].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="LOS LOC CSP FRSH FN64 W0NS W0WR"] Lemma cs_init : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pm1,P,(12.&40.)(5.(12.&8.))Ph1,(4<.Vsegs,VR,VHIA,)Pls,(1.$2.)PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)P,(37.Vsegs,VR,VHIA,R4.VLB,(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R5.)P,(4.$11.(38.Vsegs,VR,VHIA,R5.)(38.Vsegs,VR,VHIA,Vh0,))P,(4.$11.(39.Vsegs,VR,VHIA,R6.)(39.Vsegs,VR,VHIA,Vh0,))P,(4.$11.(3:.Vsegs,VR,VHIA,R7.)(3:.Vsegs,VR,VHIA,Vh0,))P,Px,$11.P,(31.Vsegs,VR,VHIA,Vh0,R1.)(31.Vsegs,VR,VHIA,R:.R2.)P,(14.(3;.Vsegs,VR,VHIA,R9.)(3;.Vsegs,VR,VHIA,Vh0,))P,(14.(3<.Vsegs,VR,VHIA,R:.)(3<.Vsegs,VR,VHIA,Vh0,))P,(2;.Vsegs,R<.VLB,VdW0,)P,(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,R<.)R=.(22.VdW0,)+10.)P,(1>.$2.Le,$2.(1?.(2;.Vsegs,R?.VLB,R1.)(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,R>.)R?.(22.R1.)+10.))Ves,)P,(1:.Vsegs,VR,(41.VLB,VdW0,)VLF,VSP,(1;.VR,)(39.Vsegs,VR,VHIA,Vh0,)(1<.(10.$11.$11.)(1=.$11.$11.(22.VdW0,)(15.(22.VdW0,)+10.))(42.(10.$11.$11.)))Vm0,R?.)P,(44.Vsegs,R10.)P,(45.Vsegs,R11.Vlo,VSPc,)P,(1>.$2.Ld,$2.(1?.(46.Vsegs,R13.(22.R1.)(55.=(56.&40.+1.)=(32.R1.)))(1?.(4.$23.(24.R1.)$2:.)(1?.(4.$11.(26.R1.)=)(1?.(4.$11.(28.R1.)=)(1?.(4.(1.(12.&40.))(57.R1.)(42.(12.&40.)))(1?.(4.$11.(58.R1.)+1.)(1?.(2=.(22.R1.))(1?.(4.$11.(2>.(22.R1.)+8.)=)(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,R12.)R13.(22.R1.)+10.)))))))))R10.)P,(3>.R11.)P,(1>.(10.$11.(1.$33.))Lac,(10.$11.(1.$33.))(46.Vsegs,R15.(16.$11.(1.$33.)R1.)(17.$11.(1.$33.)R1.))R11.)P,(1>.(10.$11.(1.$33.))(47.R13.)R12.)P,(46.Vsegs,R16.(15.(48.VFB,+3.)(49.(30.VR,)))R12.)P,(14.(27.+8.(34.(35.R13.)))VFN,)(51.R18.R17.VLB,R16.VdW0,R15.R14.==)")
(* [comment removed for export] *).
  Proof.
    intros m1 h1 ls CS SHC HH HT HS HF HCS HV HFR MW0 OW0 EXT PX MI1 ST1 LOC0 SA CH CHS SHD SHN.
    dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    assert (NOBLK : forall b, ~ In b (flat_map mpd_blk ls)).
    { intros b Hb. apply in_flat_map in Hb. ddestruct Hb as (d & Hd & Hb). pose proof (proj1 (Forall_forall _ _) LOC0 d Hd) as (_ & O & _). unfold mpd_blk in Hb. rewrite O in Hb. exact Hb. }
    unfold cstateA.
    split; [exact HH|]. split; [exact (conj HT (conj HS HF))|]. split; [exact HCS|]. split; [split; [clear - HV; lia| clear - HFR; lia]|].
    split.
    { apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) LOC0 d Hd) as (RC & O & P0 & N0 & L0 & S1 & AL1 & A8 & OD).
      split; [| split; [rewrite O; discriminate| split; [exact AL1| split; [exact A8| exact OD]]]].
      split; [| rewrite S1; left; reflexivity].
      split; [rewrite P0, S1, N0; exact RC|]. split; [exact A8|]. split; [pose proof (alloc_ceiling_pos (L := L)) as ACP; destruct AL1 as [[A1 A2]|[A1 A2]]; [clear - A1 F0; lia| clear - A1 LOC LOS ALO ACP; lia]|]. split; [rewrite L0, N0; reflexivity|]. split; [rewrite N0; unfold MPI_MAX_LIMBS; clear; lia|].
      rewrite O. split; assumption. }
    split; [exact SA|].
    split. { intros a b da db Ha Hb NE Oa. pose proof (proj1 (Forall_forall _ _) LOC0 da (nth_error_In _ _ Ha)) as (_ & O & _). congruence. }
    split; [exact MW0|]. split; [exact OW0|].
    split.
    { split; [reflexivity|]. split; [exact W0NS|]. split; [split; [reflexivity| clear; lia]|]. split.
      - intros O. split; [exact (NOBLK _)|]. left. apply mpd_blk_in. exact O.
      - intros b Hb _. left. reflexivity. }
    split; [intros b Hb _; exact Hb|]. split; [intros b Hb; left; exact Hb|]. split; [intros b Hb; destruct (NOBLK b Hb)|].
    split; [exact EXT|]. split; [exact PX|]. split; [intros b Hb; destruct (NOBLK b Hb)|]. split; [intros b Hb; left; exact Hb|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact CH|]. split; [exact CHS|]. split; [exact SHD| exact SHN].
  Qed.

  #[using="Type"] Lemma mpd_heap_in : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))PLBq,(1.$3.)Pd,$2.P,(2;.Vsegs,R3.R2.R1.)P,(4.$23.(24.R2.)$25.)(1?.(8.(10.$11.$11.)(1=.$11.$11.(26.R3.)(27.+4.(28.R3.)))R4.)(14.+1.(28.R3.)))")
(* [comment removed for export] *).
  Proof. intros mq LBq d [(_ & _ & _ & _ & _ & OWN) _] O. rewrite O in OWN. ddestruct OWN as (N1 & IN & _). split; assumption. Qed.

  #[using="Type"] Lemma fresh_apart_unframe : forall LBx N k, fresh_apart R LBx LF' N k -> fresh_apart R LBx LF N k.
  Proof.
    (intros LBx N k dd_H; ddestruct dd_H as (G0 & G1 & G2 & G3)). split; [exact G0|]. split; [exact G1|]. split; [exact G2|].
    intros B j Hb. apply G3. apply fdata_cons_sub. exact Hb.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma keep0_sub_local : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pi,$0.PdX,$2.P,(51.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4.(5.$2.)(6.$2.R9.R3.)(7.$2.R2.))Pb,$3.P,(8.$3.R1.(41.VLB,VdW0,))(8.$3.R2.(41.R=.R5.))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f i dX CST Hi b Hb. dest_cs CST.
    apply In_mpd_keep_intro; [apply SUB; [eapply In_mpd_keep; exact Hb| exact (In_mpd_keep_not_blk_w _ _ _ Hb)]|].
    intros HX. apply (In_mpd_keep_not_blk_w _ _ _ Hb). apply FRS; [| eapply In_mpd_keep; exact Hb].
    apply in_flat_map. exists dX. split; [eapply nth_error_In; exact Hi| exact HX].
  Qed.

  (* [comment removed for export] *)
  #[using="segs HIA h0 lo SPc LOC CSP W0WR W0AS"] Lemma w0_client_step : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "PLBk,(1.$3.)PSPx,$11.P,Pb,$3.P,(8.$3.R1.(41.VLB,VdW0,))(8.$3.R2.R4.)P,(14.R2.VSP,)(20.(19.VR,)(13.$3.R4.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))R3.(22.VdW0,)+10.)")
(* [comment removed for export] *).
  Proof.
    intros LBk SPx KS HSX x Hx. destruct (w0_client x Hx) as [X|[X|(b & Hb & Rb)]].
    - left. destruct W0AS as [C|C]; [exfalso; clear - C X Hx; lia| clear - C Hx HSX; lia].
    - right; left; exact X.
    - right; right. exists b. split; [| exact Rb]. apply in_app_iff in Hb. apply in_app_iff.
      destruct Hb as [Hb|Hb]; [left; exact (KS b Hb)| right; cbn [fdata]; right; right; exact Hb].
  Qed.

  #[using="lo ESF"] Lemma ext_client_step : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pe,$2.PLBk,(1.$3.)PSPx,$11.P,(8.$2.R3.Ves,)P,Pb,$3.P,(8.$3.R1.(41.VLB,VdW0,))(8.$3.R2.R5.)P,(14.R3.VSP,)(20.(19.VR,)(13.$3.R5.(21.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)))R4.(22.R6.)+10.)")
(* [comment removed for export] *).
  Proof.
    intros e LBk SPx He KS HSX x Hx.
    pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE & INE & ASE & E4 & E5 & E6 & E7).
    destruct (CRE x Hx) as [X|[X|(b & Hb & Rb)]].
    - left. destruct ASE as [C|C]; [exfalso; clear - C X Hx; lia| clear - C Hx HSX; lia].
    - right; left; exact X.
    - right; right. exists b. split; [| exact Rb]. apply in_app_iff in Hb. apply in_app_iff.
      destruct Hb as [Hb|Hb]; [left| right; cbn [fdata]; right; right; exact Hb].
      apply KS. apply In_mpd_keep_intro; [exact Hb|]. intros K. destruct (mpd_blk_heap _ _ K) as [O0 E]. subst b. cbn [fst snd] in Rb.
      specialize (E4 O0). clear - E4 Rb Hx. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="LOS LOC CSP FRSH FN64 W0WR ESF"] Lemma ext_step : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pm2,P,(12.&40.)(5.(12.&8.))Ph2,(4<.Vsegs,VR,VHIA,)PLB2,(1.$3.)PLBk,(1.$3.)PSPx,$11.PWX,(1.$4=.)P,(51.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(1:.Vsegs,VR,R4.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R3.(1;.VR,)(39.Vsegs,VR,VHIA,R?.)R2.R10.R7.)P,(44.Vsegs,R8.)P,Px,$11.P,(31.Vsegs,VR,VHIA,R12.R1.)(31.Vsegs,VR,VHIA,R:.R2.)P,(14.VSPc,R6.)P,(14.R7.VSP,)P,Pb,$3.P,(8.$3.R1.(41.VLB,VdW0,))(8.$3.R2.R;.)P,Pb,$3.P,(8.$3.R1.(41.VLB,VdW0,))(8.$3.R2.R=.)P,Pe,$2.P,(8.$2.R1.Ves,)(1?.(4>.R;.(22.R2.)+10.)P,(4.$23.(24.R2.)$25.)(4>.R<.(26.R3.)(27.+4.(28.R3.))))(1>.$2.Le,$2.(1?.(2;.Vsegs,R10.R>.R1.)(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,R?.)R10.(22.R1.)+10.))Ves,)")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f m2 h2 LB2 LBk SPx WX CST HP MI2 HCS2 HS1 HS2 KS KS2 DJ.
    apply Forall_forall. intros e He.
    destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST He) as (ME & OE & _ & _ & HFE & _).
    destruct (DJ e He) as [D1 D2]. dest_cs CST.
    eapply (mpd_step mq m2 hq h2 LBq LBk LB2 SPx WX e ME OE HP MI MI2 HCS2 ltac:(clear - HS1 LOS LOC; lia)
              (ext_client_step e LBk SPx He KS HS2)); [| exact D1| exact D2|].
    - intros O. apply KS. exact (proj1 (proj2 (HFE O))).
    - intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. apply KS2. exact (proj1 (proj2 (HFE O))).
  Qed.

  (* [comment removed for export] *)
  #[using="segs HIA h0 SP lo SPc FB FN LOS LOC CSP FRSH FN64 W0WR ESF"] Lemma fresh_vs_ext : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pe,$2.PN,$11.Pk,$11.P,(8.$2.R3.Ves,)P,(43.VR,(41.VLB,VdW0,)VLF,R3.R2.)P,(4;.=R3.)(1?.(;.(14.(15.R5.R4.)(22.R6.))(14.(15.(22.R6.)+10.)R5.))P,(4.$23.(24.R6.)$25.)(;.(14.(15.R6.R5.)(26.R7.))(14.(15.(26.R7.)(27.+4.(28.R7.)))R6.)))")
(* [comment removed for export] *).
  Proof.
    intros e N k He FR Hk. dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE & INE & ASE & E4 & E5 & E6 & E7).
    split.
    - assert (CRk : client_range L (KEEP0 ++ fdata LF) lo (md_addr e) 16).
      { intros x Hx. destruct (CRE x Hx) as [X|[X|(b & Hb & Rb)]]; [left; exact X| right; left; exact X| right; right; exists b; split; [| exact Rb]].
        apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
        apply In_mpd_keep_intro; [exact Hb|]. intros K. destruct (mpd_blk_heap _ _ K) as [O0 E]. subst b. cbn [fst snd] in Rb.
        specialize (E4 O0). clear - E4 Rb Hx. lia. }
      exact (fresh_apart_client R KEEP0 LF lo (md_addr e) 16 N k FR CRk ltac:(clear; lia) Hk ltac:(clear - ALO LOS; lia)).
    - intros O. destruct (INE O) as [IN N1]. ddestruct FR as (_ & _ & _ & G3).
      apply (G3 (md_p e) (4 * md_n e)). apply in_app_iff. left. apply In_mpd_keep_intro; [exact IN|].
      intros K. destruct (mpd_blk_heap _ _ K) as [O0 E]. injection E as E1 E2.
      destruct E5 as [C|[C|C]]; [exact (C O0)| rewrite O in C; discriminate C| clear - C E1 E2 N1; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="LOS LOC CSP FRSH FN64 W0WR ESF"] Lemma loc_vs_ext : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pe,$2.PA,$11.P,(51.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(8.$2.R3.Ves,)P,(2=.R3.)(1?.(;.(14.(15.R4.+10.)(22.R5.))(14.(15.(22.R5.)+10.)R4.))P,(4.$23.(24.R5.)$25.)(;.(14.(15.(26.R6.)(27.+4.(28.R6.)))R5.)(14.(15.R5.+10.)(26.R6.))))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f e A CST He HA.
    destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST He) as (_ & _ & _ & _ & HFE & ASE & EFB).
    dest_cs CST. split.
    - destruct HA as [[H1 H2]|[H1 H2]]; [clear - H1 H2 EFB FN64; lia| clear - H1 H2 ASE LOC; lia].
    - intros O. ddestruct (HFE O) as (INq & _ & _). destruct (blk_facts _ _ _ _ _ HH INq) as (_ & BC & BF).
      exact (loc_vs_low _ _ _ HA BC BF).
  Qed.

  (* [comment removed for export] *)
  #[using="h0 LB lo dW0 LOS LOC CSP FRSH FN64 W0WR"] Lemma loc_vs_blk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)PA,$11.PB,$11.Pk,$11.P,(37.Vsegs,VR,VHIA,R5.R4.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R6.)P,(8.(10.$11.$11.)(1=.$11.$11.R3.R2.)R5.)P,(2=.R5.)(;.(14.(15.R5.R4.)R6.)(14.(15.R6.+10.)R5.))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq A B k HH Hb HA. destruct (blk_facts _ _ _ _ _ HH Hb) as (_ & BC & BF). exact (loc_vs_low _ _ _ HA BC BF).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HND DIMG H0M LOS LOC CSP SPT FRSH FN64 FB8 W0WR W0AS ESF"] Lemma cs_binop_l : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pi,$0.PdX,$2.Pm2,P,(12.&40.)(5.(12.&8.))Ph2,(4<.Vsegs,VR,VHIA,)PLB2,(1.$3.)PdX',$2.Pdv,$11.Pdf,$11.P,(51.R11.R10.R?.R>.R=.R<.R;.R:.R9.)P,(4.(5.$2.)(6.$2.R?.R9.)(7.$2.R8.))P,(37.Vsegs,VR,VHIA,R7.R6.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R8.)P,(4.$11.(38.Vsegs,VR,VHIA,R8.)(38.Vsegs,VR,VHIA,R13.))P,(4.$11.(39.Vsegs,VR,VHIA,R9.)(39.Vsegs,VR,VHIA,R14.))P,(4.$11.(3:.Vsegs,VR,VHIA,R:.)(3:.Vsegs,VR,VHIA,R15.))P,Px,$11.P,(31.Vsegs,VR,VHIA,R17.R1.)(31.Vsegs,VR,VHIA,R=.R2.)P,(14.(3;.Vsegs,VR,VHIA,R<.)(15.(3;.Vsegs,VR,VHIA,R17.)R9.))P,(14.(3<.Vsegs,VR,VHIA,R=.)(15.(3<.Vsegs,VR,VHIA,R18.)R9.))P,(2;.Vsegs,R?.R=.R<.)P,(53.R19.R11.R>.R=.)P,(1:.Vsegs,VR,(41.R1:.R12.)(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)VSPc,(1;.VR,)(39.Vsegs,VR,VHIA,R1;.)(1<.(10.$11.$11.)(1=.$11.$11.(22.R12.)(15.(22.R12.)+10.))(42.(10.$11.$11.)))R1<.R11.)P,(44.Vsegs,R12.)P,(45.Vsegs,R13.Vlo,VSPc,)P,Pb,$3.P,(8.$3.R1.(:.R12.))(;.(8.$3.R2.(:.R17.))(29.(8.$3.R2.R1?.)))P,Pb,$3.P,(8.$3.R1.(:.R13.))(;.(8.$3.R2.(:.R18.))(43.VR,(41.R20.R18.)(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)(16.$11.$11.R2.)(17.$11.$11.R2.)))(51.R16.R15.R14.(59.$2.R18.R1>.R13.)R1=.R1<.R1;.(15.R1:.R12.)(15.R19.R11.))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f i dX m2 h2 LB2 dX' dv df CST Hi HH2 HT2 HS2 HF2 HCS2 HV2 HFR2 MA2 OUT HP MI2 ST2 FRESH FRESHA.
    dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MX & NSX & _ & _ & _ & _ & HFX & XDL & XD8 & _ & OX).
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (_ & NSW & EA & _ & _ & _ & _ & HFW & ASW & _ & _).
    pose proof (keep0_sub_local _ _ _ _ _ _ _ _ _ _ _ CST Hi) as KS.
    pose proof CST as CST'. dest_cs CST. ddestruct WOK as (_ & _ & EP & WB & WK).
    dpose OUT as (EAX & NS & K1 & K2 & K3).
    pose proof (nth_error_In _ _ Hi) as INX.
    pose proof (HND _ _ _ _ HH) as NDq. pose proof (HND _ _ _ _ HH2) as ND2.
    assert (XB : forall b, In b (mpd_blk dX) -> In b (flat_map mpd_blk ls)) by (intros b Hb; apply in_flat_map; exists dX; split; [exact INX| exact Hb]).
    assert (KEEPJ : forall j dj, nth_error ls j = Some dj -> j <> i -> forall b, In b (mpd_blk dj) -> In b (mpd_keep LBq dX) /\ In b LB2).
    { intros j dj Hj NE b Hb. destruct (mpd_blk_heap _ _ Hb) as [OJ ->].
      pose proof (proj1 (Forall_forall _ _) LOK dj (nth_error_In _ _ Hj)) as (MJ & _).
      assert (NX : ~ In (md_p dj, 4 * md_n dj) (mpd_blk dX)).
      { intros HX. destruct (mpd_blk_heap _ _ HX) as [OX' E]. injection E as E1 E2. exact (LA _ _ _ _ Hj Hi NE OJ OX' E1). }
      split; [apply In_mpd_keep_intro; [exact (proj1 (mpd_heap_in _ _ _ MJ OJ))| exact NX]| apply K2; [exact (proj1 (mpd_heap_in _ _ _ MJ OJ))| exact NX]]. }
    assert (KEEPW : forall b, In b (mpd_blk dW) -> In b (mpd_keep LBq dX) /\ In b LB2).
    { intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [OWh ->].
      assert (NX : ~ In (md_p dW, 4 * md_n dW) (mpd_blk dX)) by (intros HX; apply (proj1 (WB OWh)); exact (XB _ HX)).
      split; [apply In_mpd_keep_intro; [exact (proj1 (mpd_heap_in _ _ _ MW OWh))| exact NX]| apply K2; [exact (proj1 (mpd_heap_in _ _ _ MW OWh))| exact NX]]. }
    assert (SUB2 : forall b, In b LB -> ~ In b (mpd_blk dW0) -> In b LB2).
    { intros b Hb NW. apply K2; [exact (SUB b Hb NW)|]. intros C. exact (NW (FRS _ (XB _ C) Hb)). }
    assert (KS2 : forall b, In b KEEP0 -> In b LB2) by (intros b Hb; apply SUB2; [eapply In_mpd_keep; exact Hb| exact (In_mpd_keep_not_blk_w _ _ _ Hb)]).
    assert (NEWX : forall b, In b (mpd_blk dX') -> ~ In b LBq -> In b LB -> In b (mpd_blk dW0)).
    { intros b Hb NQ HL. destruct (in_dec blk_eq_dec2 b (mpd_blk dW0)) as [Y|N]; [exact Y|]. exfalso. exact (NQ (SUB _ HL N)). }
    (* [comment removed for export] *)
    assert (DJX : forall A k, (A + k <= md_addr dX \/ md_addr dX + 16 <= A) -> disjoint_from [(md_addr dX, md_addr dX + 16)] A k).
    { intros A k HA. cbn [disjoint_from]. split; [clear - HA; lia| exact I]. }
    assert (BLKX : forall B k, In (B, k) LBq -> B + k <= md_addr dX \/ md_addr dX + 16 <= B).
    { intros B k Hb. exact (loc_vs_blk _ _ _ _ _ _ HH Hb XDL). }
    unfold cstateA.
    split; [exact HH2|]. split; [rewrite HT2, HS2, HF2; exact (conj HTc (conj HSc HFc))|]. split; [intros x Hx; exact (HCS2 x (HCSc x Hx))|].
    split; [split; [clear - HV2 HVc; lia| clear - HFR2 HFRc; lia]|].
    split.
    { (* [comment removed for export] *)
      eapply Forall_set_nth; [exact Hi| |].
      - split; [exact MA2|]. split; [exact NS|]. rewrite EAX. split; [exact XDL|]. split; [exact XD8|].
        eapply aobj_cs_mono; [exact HCS2|].
        eapply (presA_aobj segs R); [exact (hcs_ok segs R HIA hq)| exact HP| exact OX| apply loc_client; [exact XDL| intros K; exact K]| clear - LOS LOC; lia| intros x Hx; eapply hcs_below_top; exact Hx].
      - intros j dj Hj NE. pose proof (proj1 (Forall_forall _ _) LOK dj (nth_error_In _ _ Hj)) as (MJ & NSJ & JL & JA8 & OJ).
        destruct (mpd_step mq m2 hq h2 LBq (mpd_keep LBq dX) LB2 SPc _ dj MJ OJ HP MI MI2 HCS2 ltac:(clear - LOS LOC; lia)
                    (loc_client _ _ _ JL (fun K => K))) as [MJ2 OJ2].
        + intros O. exact (proj1 (KEEPJ _ _ Hj NE _ (mpd_blk_in _ O))).
        + apply DJX. exact (SA _ _ _ _ Hj Hi NE).
        + intros O. apply DJX. destruct (BLKX _ _ (proj1 (mpd_heap_in _ _ _ MJ O))) as [K|K]; [left; exact K| right; exact K].
        + intros b Hb. exact (proj2 (KEEPJ _ _ Hj NE _ Hb)).
        + split; [exact MJ2|]. split; [exact NSJ|]. split; [exact JL|]. split; [exact JA8| exact OJ2]. }
    split.
    { (* [comment removed for export] *)
      intros a b da db Ha Hb NE.
      destruct (set_nth_cases _ _ _ _ _ _ Hi Ha) as [[-> ->]|[NA Ha']]; destruct (set_nth_cases _ _ _ _ _ _ Hi Hb) as [[-> ->]|[NB Hb']]; [congruence| | |].
      - rewrite EAX. exact (SA _ _ _ _ Hi Hb' ltac:(congruence)).
      - rewrite EAX. exact (SA _ _ _ _ Ha' Hi ltac:(congruence)).
      - exact (SA _ _ _ _ Ha' Hb' NE). }
    split.
    { (* [comment removed for export] *)
      assert (NEWAP : forall j dj, nth_error ls j = Some dj -> j <> i -> md_own dX' = LHeap -> md_own dj = LHeap -> md_p dX' <> md_p dj).
      { intros j dj Hj NE OX' OJ E.
        pose proof (proj1 (Forall_forall _ _) LOK dj (nth_error_In _ _ Hj)) as (MJ & _).
        destruct (mpd_heap_in _ _ _ MJ OJ) as (INJ & NJ1). destruct (mpd_heap_in _ _ _ MA2 OX') as (INX' & NX1).
        pose proof (proj2 (KEEPJ _ _ Hj NE _ (mpd_blk_in _ OJ))) as INJ2.
        destruct (FRESH _ (mpd_blk_in _ OX')) as [OLD|NEW].
        - destruct (mpd_blk_heap _ _ OLD) as [OXh EE]. injection EE as P1 P2. apply (LA _ _ _ _ Hi Hj ltac:(congruence) OXh OJ). congruence.
        - destruct (blk_eq_dec2 (md_p dX', 4 * md_n dX') (md_p dj, 4 * md_n dj)) as [Q|Q]; [apply NEW; rewrite Q; exact INJ|].
          exact (nodup_fst_neq _ _ _ _ _ ND2 INJ2 INX' Q E). }
      intros a b da db Ha Hb NE Oa Ob.
      destruct (set_nth_cases _ _ _ _ _ _ Hi Ha) as [[-> ->]|[NA Ha']]; destruct (set_nth_cases _ _ _ _ _ _ Hi Hb) as [[-> ->]|[NB Hb']]; [congruence| | |].
      - exact (NEWAP _ _ Hb' ltac:(congruence) Oa Ob).
      - intros E. exact (NEWAP _ _ Ha' ltac:(congruence) Ob Oa (eq_sym E)).
      - exact (LA _ _ _ _ Ha' Hb' NE Oa Ob). }
    (* [comment removed for export] *)
    destruct (mpd_step mq m2 hq h2 LBq (mpd_keep LBq dX) LB2 SPc _ dW MW ltac:(rewrite EA; exact OW) HP MI MI2 HCS2 ltac:(clear - LOS LOC; lia)
                ltac:(rewrite EA; exact (w0_client_step _ SPc KS CSP))) as [MW2 OW2].
    { intros O. exact (proj1 (KEEPW _ (mpd_blk_in _ O))). }
    { apply DJX. rewrite EA. destruct (loc_vs_w _ XDL) as [K|K]; [right; exact K| left; exact K]. }
    { intros O. apply DJX. destruct (BLKX _ _ (proj1 (mpd_heap_in _ _ _ MW O))) as [K|K]; [left; exact K| right; exact K]. }
    { intros b Hb. exact (proj2 (KEEPW _ Hb)). }
    split; [exact MW2|]. split; [rewrite <- EA; exact OW2|].
    split.
    { (* [comment removed for export] *)
      split; [exact EA|]. split; [exact NSW|]. split; [exact EP|]. split.
      - intros OWh. destruct (WB OWh) as (WNL & WOR). split; [| exact WOR].
        intros HIn. apply (proj1 (set_nth_blk _ _ _ _ _ Hi)) in HIn. destruct HIn as [HbX'|(j & dj & Hj & NE & Hbj)].
        + destruct (FRESH _ HbX') as [OLD|NEW]; [apply WNL; exact (XB _ OLD)|].
          exact (NEW (proj1 (mpd_heap_in _ _ _ MW OWh))).
        + apply WNL. apply in_flat_map. exists dj. split; [eapply nth_error_In; exact Hj| exact Hbj].
      - intros b Hb0 Hb2. destruct (K1 b Hb2) as [Hbq|HbX'].
        + destruct (WK b Hb0 Hbq) as [E|Hl]; [left; exact E| right].
          apply in_flat_map in Hl. ddestruct Hl as (x & Hx & Hbx). destruct (In_nth_error _ _ Hx) as [j Hj].
          destruct (Nat.eq_dec j i) as [->|NE].
          * rewrite Hi in Hj. injection Hj as ->. apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). left. rewrite (K3 b Hbx Hb2). exact Hbx.
          * apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). right. dexists j, x. auto.
        + right. apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). left. exact HbX'. }
    split; [exact SUB2|].
    split.
    { (* [comment removed for export] *)
      intros b Hb. destruct (K1 b Hb) as [Hq|Hn].
      - destruct (COV b Hq) as [Hl|[Hf|Hw]]; [left; exact Hl| right; left| right; right; exact Hw].
        apply in_flat_map in Hf. ddestruct Hf as (d & Hd & Hbd). destruct (In_nth_error _ _ Hd) as [j Hj].
        destruct (Nat.eq_dec j i) as [->|NE].
        + rewrite Hi in Hj. injection Hj as ->. apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). left. rewrite (K3 b Hbd Hb). exact Hbd.
        + apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). right. dexists j, d. auto.
      - right; left. apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). left. exact Hn. }
    split.
    { (* [comment removed for export] *)
      intros b Hb HL. apply (proj1 (set_nth_blk _ _ _ _ _ Hi)) in Hb. destruct Hb as [HbX'|(j & dj & Hj & NE & Hbj)].
      - destruct (FRESH _ HbX') as [OLD|NEW]; [exact (FRS _ (XB _ OLD) HL)| exact (NEWX _ HbX' NEW HL)].
      - apply FRS; [| exact HL]. apply in_flat_map. exists dj. split; [eapply nth_error_In; exact Hj| exact Hbj]. }
    split.
    { (* [comment removed for export] *)
      eapply (ext_step mq hq LBq ls dW CS SHC v f m2 h2 LB2 (mpd_keep LBq dX) SPc _ CST' HP MI2 HCS2 ltac:(clear; lia) CSP KS KS2).
      intros e He. destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (_ & _ & _ & _ & HFE & _ & EFB).
      split; [apply DJX; destruct (proj1 (loc_vs_ext _ _ _ _ _ _ _ _ _ _ _ CST' He XDL)) as [K|K]; [right; exact K| left; exact K]|].
      intros O. apply DJX. destruct (BLKX _ _ (proj1 (HFE O))) as [K|K]; [left; exact K| right; exact K]. }
    split.
    { (* [comment removed for export] *)
      eapply (pres_step mq m2 hq (mpd_keep LBq dX) SPc _ PX HP HSc KS CSP).
      apply Forall_cons; [| apply Forall_nil]. exact (loc_wx _ XDL). }
    split.
    { (* [comment removed for export] *)
      intros b Hb. apply (proj1 (set_nth_blk _ _ _ _ _ Hi)) in Hb. destruct Hb as [HbX'|(j & dj & Hj & NE & Hbj)].
      - destruct (FRESHA _ HbX') as [OLD|NEW]; [exact (FRL _ (XB _ OLD))|].
        apply fresh_apart_unframe. eapply fresh_apart_blocks_mono; [exact NEW| exact KS].
      - apply FRL. apply in_flat_map. exists dj. split; [eapply nth_error_In; exact Hj| exact Hbj]. }
    split; [exact FRW|]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { (* [comment removed for export] *)
      eapply (cells_step mq m2 hq (mpd_keep LBq dX) SPc _ ls CS HP CH CHS).
      apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as [[[C1 C2]|[[C1 C2]|[C1 C2]]] C3].
      - split; [left; exact C1|]. apply DJX. destruct (C3 dX INX) as [K|K]; [left; exact K| right; exact K].
      - split; [right; clear - C1 C2 FN64; lia|]. apply DJX. destruct (C3 dX INX) as [K|K]; [left; exact K| right; exact K].
      - split; [right; clear - C1 C2; lia|]. apply DJX. destruct (C3 dX INX) as [K|K]; [left; exact K| right; exact K]. }
    split.
    { apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as [CL C3]. split; [exact CL|].
      intros d Hd. destruct (In_set_nth_inv _ _ _ _ _ Hi Hd) as [->|(j & Hj & NE)]; [rewrite EAX; exact (C3 dX INX)| exact (C3 d (nth_error_In _ _ Hj))]. }
    split; [| exact SHN].
    eapply (shadow_step mq m2 hq (mpd_keep LBq dX) SPc _ SHC); [right| exact HP| exact SHD| exact SHN].
    intros x Hx. replace x with (FB + (x - FB)) by (clear; lia). eapply (hcs_fake segs R HIA hq _ _ mq FB FN HH); [left; reflexivity| clear - Hx; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="HND DIMG H0M LOS LOC CSP SPT FRSH FN64 FB8 W0WR W0AS ESF"] Lemma cs_binop_w : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pm2,P,(12.&40.)(5.(12.&8.))Ph2,(4<.Vsegs,VR,VHIA,)PLB2,(1.$3.)PdW',$2.Pdv,$11.Pdf,$11.PSPx,$11.P,(51.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(37.Vsegs,VR,VHIA,R7.R6.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R8.)P,(4.$11.(38.Vsegs,VR,VHIA,R8.)(38.Vsegs,VR,VHIA,R11.))P,(4.$11.(39.Vsegs,VR,VHIA,R9.)(39.Vsegs,VR,VHIA,R12.))P,(4.$11.(3:.Vsegs,VR,VHIA,R:.)(3:.Vsegs,VR,VHIA,R13.))P,Px,$11.P,(31.Vsegs,VR,VHIA,R15.R1.)(31.Vsegs,VR,VHIA,R=.R2.)P,(14.(3;.Vsegs,VR,VHIA,R<.)(15.(3;.Vsegs,VR,VHIA,R15.)R9.))P,(14.(3<.Vsegs,VR,VHIA,R=.)(15.(3<.Vsegs,VR,VHIA,R16.)R9.))P,(2;.Vsegs,R?.R=.R<.)P,(2?.Vsegs,(30.VR,)(31.Vsegs,VR,VHIA,R?.)R10.(22.VdW0,)+10.)P,(53.R18.R16.R?.R>.)P,(1:.Vsegs,VR,(41.R19.R17.)(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R<.(1;.VR,)(39.Vsegs,VR,VHIA,R1:.)(1<.(10.$11.$11.)(1=.$11.$11.(22.VdW0,)(15.(22.VdW0,)+10.))(42.(10.$11.$11.)))R1;.R12.)P,(14.VSPc,R=.)P,(14.R>.VSP,)P,(44.Vsegs,R15.)P,(45.Vsegs,R16.Vlo,VSPc,)P,Pb,$3.P,(8.$3.R1.(:.R15.))(;.(8.$3.R2.(:.R1>.))(29.(8.$3.R2.R20.)))P,Pb,$3.P,(8.$3.R1.(:.R16.))(;.(8.$3.R2.(:.R1?.))(43.VR,(41.R21.R1?.)(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)(16.$11.$11.R2.)(17.$11.$11.R2.)))P,(4.(12.&40.)(32.R16.)(32.R1>.))P,(14.(28.R1?.)(28.R17.))P,(1>.(10.$11.(1.$33.))Lac,(10.$11.(1.$33.))(;.(14.R16.(16.$11.(1.$33.)R1.))(4;.(16.$11.(1.$33.)R1.)(15.VFB,VFN,)))R1?.)P,(1>.$2.Ld,$2.P,(14.VSPc,(22.R1.))(14.R18.(22.R2.))R22.)(51.R1=.R1<.R1;.R23.R1:.R21.R20.(15.R1?.R19.)(15.R1>.R18.))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f m2 h2 LB2 dW' dv df SPx CST HH2 HT2 HS2 HF2 HCS2 HV2 HFR2 MA2 OW2 OUT HP HX1 HX2 MI2 ST2 FRESH FRESHA PAD NLE CSX LSX.
    dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (_ & NSW & EA & _ & _ & _ & _ & HFW & ASW & _ & _).
    pose proof CST as CST'. dest_cs CST. ddestruct WOK as (_ & _ & [EP EN] & WB & WK).
    dpose OUT as (EAX & NS & K1 & K2 & K3).
    pose proof (HND _ _ _ _ HH) as NDq. pose proof (HND _ _ _ _ HH2) as ND2.
    assert (WNL : forall b, In b (mpd_blk dW) -> ~ In b (flat_map mpd_blk ls)).
    { intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [OWh ->]. exact (proj1 (WB OWh)). }
    assert (WLB : forall b, In b (mpd_blk dW) -> In b LB -> In b (mpd_blk dW0)).
    { intros b Hb HL. destruct (mpd_blk_heap _ _ Hb) as [OWh ->]. destruct (proj2 (WB OWh)) as [Y|N]; [exact Y| exfalso; exact (N HL)]. }
    assert (KEEPJ : forall dj, In dj ls -> forall b, In b (mpd_blk dj) -> In b (mpd_keep LBq dW) /\ In b LB2).
    { intros dj Hdj b Hb. destruct (mpd_blk_heap _ _ Hb) as [OJ ->].
      pose proof (proj1 (Forall_forall _ _) LOK dj Hdj) as (MJ & _).
      assert (NW : ~ In (md_p dj, 4 * md_n dj) (mpd_blk dW)).
      { intros HW. apply (WNL _ HW). apply in_flat_map. exists dj. split; [exact Hdj| apply mpd_blk_in; exact OJ]. }
      split; [apply In_mpd_keep_intro; [exact (proj1 (mpd_heap_in _ _ _ MJ OJ))| exact NW]| apply K2; [exact (proj1 (mpd_heap_in _ _ _ MJ OJ))| exact NW]]. }
    assert (SUB2 : forall b, In b LB -> ~ In b (mpd_blk dW0) -> In b LB2).
    { intros b Hb NW. apply K2; [exact (SUB b Hb NW)|]. intros HW. exact (NW (WLB _ HW Hb)). }
    assert (KS : forall b, In b KEEP0 -> In b (mpd_keep LBq dW)).
    { intros b Hb. apply In_mpd_keep_intro; [apply SUB; [eapply In_mpd_keep; exact Hb| exact (In_mpd_keep_not_blk_w _ _ _ Hb)]|].
      intros HW. exact (In_mpd_keep_not_blk_w _ _ _ Hb (WLB _ HW (In_mpd_keep _ _ _ Hb))). }
    assert (KS2 : forall b, In b KEEP0 -> In b LB2) by (intros b Hb; apply SUB2; [eapply In_mpd_keep; exact Hb| exact (In_mpd_keep_not_blk_w _ _ _ Hb)]).
    assert (DJW : forall A k, (A + k <= W0 \/ W0 + 16 <= A) -> disjoint_from [(W0, W0 + 16)] A k).
    { intros A k HA. cbn [disjoint_from]. split; [clear - HA; lia| exact I]. }
    unfold cstateA.
    split; [exact HH2|]. split; [rewrite HT2, HS2, HF2; exact (conj HTc (conj HSc HFc))|]. split; [intros x Hx; exact (HCS2 x (HCSc x Hx))|].
    split; [split; [clear - HV2 HVc; lia| clear - HFR2 HFRc; lia]|].
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros dj Hdj.
      pose proof (proj1 (Forall_forall _ _) LOK dj Hdj) as (MJ & NSJ & JL & JA8 & OJ).
      destruct (mpd_step mq m2 hq h2 LBq (mpd_keep LBq dW) LB2 SPx _ dj MJ OJ HP MI MI2 HCS2 ltac:(clear - HX1 LOS LOC; lia)
                  (loc_client _ _ _ JL (proj1 (Forall_forall _ _) LSX dj Hdj))) as [MJ2 OJ2].
      - intros O. exact (proj1 (KEEPJ _ Hdj _ (mpd_blk_in _ O))).
      - apply DJW. destruct (loc_vs_w _ JL) as [K|K]; [left; exact K| right; exact K].
      - intros O. apply DJW. destruct (In_nth_error _ _ Hdj) as [j Hj].
        destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST' Hj) as (_ & _ & _ & _ & _ & _ & HFJ & _).
        ddestruct (HFJ O) as (_ & _ & _ & NJ1 & _ & FRJ).
        pose proof (fresh_apart_client R KEEP0 LF lo W0 16 _ _ FRJ w0_client ltac:(clear; lia) ltac:(clear - NJ1; lia) ltac:(clear - ALO LOS; lia)) as AP.
        clear - AP. lia.
      - intros b Hb. exact (proj2 (KEEPJ _ Hdj _ Hb)).
      - split; [exact MJ2|]. split; [exact NSJ|]. split; [exact JL|]. split; [exact JA8| exact OJ2]. }
    split; [exact SA|]. split; [exact LA|].
    split; [exact MA2|]. split; [exact OW2|].
    split.
    { (* [comment removed for export] *)
      split; [rewrite EAX; exact EA|]. split; [exact NS|]. split; [split; [rewrite PAD; exact EP| clear - EN NLE; lia]|]. split.
      - intros OW'. pose proof (mpd_blk_in _ OW') as HbW'.
        destruct (FRESH _ HbW') as [OLD|NEW].
        + split; [exact (WNL _ OLD)|].
          destruct (in_dec blk_eq_dec2 (md_p dW', 4 * md_n dW') LB) as [HL|HNL]; [left; exact (WLB _ OLD HL)| right; exact HNL].
        + split.
          { intros Hl. apply in_flat_map in Hl. ddestruct Hl as (x & Hx & Hbx). destruct (mpd_blk_heap _ _ Hbx) as [OXh E].
            pose proof (proj1 (Forall_forall _ _) LOK x Hx) as (MX & _). apply NEW. rewrite E. exact (proj1 (mpd_heap_in _ _ _ MX OXh)). }
          destruct (in_dec blk_eq_dec2 (md_p dW', 4 * md_n dW') (mpd_blk dW0)) as [Y|N]; [left; exact Y| right].
          intros HL. exact (NEW (SUB _ HL N)).
      - intros b Hb0 Hb2. destruct (K1 b Hb2) as [Hbq|HbW'].
        + destruct (WK b Hb0 Hbq) as [E|Hl]; [| right; exact Hl].
          left. rewrite <- E. apply (K3 b); [rewrite E; exact Hb0| exact Hb2].
        + left. destruct (mpd_blk_heap _ _ HbW') as [OW' ->]. destruct (mpd_blk_heap _ _ Hb0) as [O0 E0].
          unfold mpd_blk. rewrite OW', O0. rewrite E0. reflexivity. }
    split; [exact SUB2|].
    split.
    { (* [comment removed for export] *)
      intros b Hb. destruct (K1 b Hb) as [Hq|Hn]; [| right; right; exact Hn].
      destruct (COV b Hq) as [Hl|[Hf|Hw]]; [left; exact Hl| right; left; exact Hf|].
      right; right. rewrite (K3 b Hw Hb). exact Hw. }
    split; [exact FRS|].
    split.
    { (* [comment removed for export] *)
      eapply (ext_step mq hq LBq ls dW CS SHC v f m2 h2 LB2 (mpd_keep LBq dW) SPx _ CST' HP MI2 HCS2 HX1 HX2 KS KS2).
      intros e He. pose proof (proj1 (Forall_forall _ _) ESF e He) as (_ & _ & _ & _ & _ & E6 & E7).
      split; [apply DJW; clear - E6; lia|]. intros O. apply DJW. specialize (E7 ltac:(rewrite O; discriminate)). clear - E7. lia. }
    split.
    { eapply (pres_step mq m2 hq (mpd_keep LBq dW) SPx _ PX HP HSc KS HX2). apply Forall_cons; [left; reflexivity| apply Forall_nil]. }
    split; [exact FRL|].
    split.
    { (* [comment removed for export] *)
      intros b Hb. destruct (FRESHA _ Hb) as [OLD|NEW]; [exact (FRW _ OLD)| right].
      apply fresh_apart_unframe. eapply fresh_apart_blocks_mono; [exact NEW| exact KS]. }
    split; [exact MI2|]. split; [exact ST2|].
    split.
    { eapply (cells_step mq m2 hq (mpd_keep LBq dW) SPx _ ls CS HP CH CHS).
      apply Forall_forall. intros ac Hac. split; [exact (proj1 (Forall_forall _ _) CSX _ Hac)|].
      pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as [[[C1 C2]|[[C1 C2]|[C1 C2]]] _]; apply DJW.
      - destruct ASW as [K|K]; [right; clear - K C1 LOC; lia| left; clear - K C2; lia].
      - clear - WFB C1 C2 FN64. lia.
      - clear - WFB C1 C2. lia. }
    split; [exact CHS|].
    split; [| exact SHN].
    eapply (shadow_step mq m2 hq (mpd_keep LBq dW) SPx _ SHC); [right| exact HP| exact SHD| exact SHN].
    intros x Hx. replace x with (FB + (x - FB)) by (clear; lia). eapply (hcs_fake segs R HIA hq _ _ mq FB FN HH); [left; reflexivity| clear - Hx; lia].
  Qed.

  #[using="FB"] Lemma remove_nth_src : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pi,$0.Pls,(1.$2.)Pdj,$2.P,(8.$2.R1.(<.$2.R3.R2.))(5:.$0.Lj,$0.(1?.(4.(5.$2.)(6.$2.R4.R1.)(7.$2.R3.))(29.(4.$0.R1.R5.))))")
(* [comment removed for export] *).
  Proof.
    intros i ls dj Hd. destruct (In_nth_error _ _ Hd) as [j' Hj]. rewrite nth_error_remove_nth in Hj.
    exists (if (j' <? i)%nat then j' else S j'). split; [exact Hj|]. destruct (j' <? i)%nat eqn:E; rewrite ?Nat.ltb_lt, ?Nat.ltb_ge in E; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HND DIMG H0M LOS LOC CSP SPT FRSH FN64 FB8 W0WR W0AS ESF"] Lemma cs_drop : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pi,$0.Pd,$2.Pm2,P,(12.&40.)(5.(12.&8.))Ph2,(4<.Vsegs,VR,VHIA,)Pdv,$11.Pdf,$11.P,(51.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(4.(5.$2.)(6.$2.R=.R7.)(7.$2.R6.))P,(4.$23.(24.R7.)$25.)P,(37.Vsegs,VR,VHIA,R6.(5;.(26.R8.)R10.)(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R7.)P,(4.$11.(38.Vsegs,VR,VHIA,R7.)(38.Vsegs,VR,VHIA,R12.))P,(4.$11.(39.Vsegs,VR,VHIA,R8.)(39.Vsegs,VR,VHIA,R13.))P,(4.$11.(3:.Vsegs,VR,VHIA,R9.)(3:.Vsegs,VR,VHIA,R14.))P,Px,$11.P,(31.Vsegs,VR,VHIA,R16.R1.)(31.Vsegs,VR,VHIA,R<.R2.)P,(14.(3;.Vsegs,VR,VHIA,R;.)(15.(3;.Vsegs,VR,VHIA,R16.)R:.))P,(14.(3<.Vsegs,VR,VHIA,R<.)(15.(3<.Vsegs,VR,VHIA,R17.)R:.))P,(1:.Vsegs,VR,(5;.(26.R?.)R17.)(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)VSPc,(1;.VR,)(39.Vsegs,VR,VHIA,R18.)(1<.(10.$11.$11.)(1=.$11.$11.(26.R?.)(15.(26.R?.)(27.+4.(28.R?.))))(42.(10.$11.$11.)))R19.R>.)P,(44.Vsegs,R?.)P,(45.Vsegs,R10.Vlo,VSPc,)(51.R11.R10.(5;.(26.R12.)R1:.)(<.$2.R13.R19.)R18.R17.R16.(15.R15.R?.)(15.R14.R>.))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f i d m2 h2 dv df CST Hi OD HH2 HT2 HS2 HF2 HCS2 HV2 HFR2 HP MI2 ST2.
    dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MD & NSD & _ & _ & _ & _ & HFD & DDL & DD8 & _ & _).
    ddestruct (HFD OD) as (PD0 & PDC & IND & ND1 & DBF & DFR).
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (_ & NSW & EA & _ & _ & _ & _ & HFW & ASW & _ & _).
    pose proof CST as CST'. dest_cs CST. ddestruct WOK as (WK1 & WK2 & EP & WB & WK).
    pose proof (HND _ _ _ _ HH) as NDq.
    set (LB2 := lb_remove (md_p d) LBq) in *.
    destruct (hm_apart segs R HIA hq LBq LF' mq HH) as [_ BA].
    assert (BAq : blocks_apart LBq) by (eapply blocks_apart_app_l; exact BA).
    assert (NINf : forall k, ~ In (md_p d, k) LB2) by (intros k; subst LB2; apply lb_remove_notin; exact NDq).
    assert (KEEP : forall b, In b LBq -> b <> (md_p d, 4 * md_n d) -> In b LB2).
    { intros [B k] Hb NE. subst LB2. apply In_lb_remove_keep; [exact Hb|]. exact (nodup_fst_neq _ _ _ _ _ NDq IND Hb NE). }
    assert (BACK : forall b, In b LB2 -> In b LBq) by (intros b Hb; subst LB2; eapply In_lb_remove; exact Hb).
    assert (DB : In (md_p d, 4 * md_n d) (flat_map mpd_blk ls)) by (apply in_flat_map; exists d; split; [eapply nth_error_In; exact Hi| apply mpd_blk_in; exact OD]).
    assert (KS : forall b, In b KEEP0 -> In b LB2).
    { intros b Hb. apply KEEP; [apply SUB; [eapply In_mpd_keep; exact Hb| exact (In_mpd_keep_not_blk_w _ _ _ Hb)]|].
      intros ->. exact (In_mpd_keep_not_blk_w _ _ _ Hb (FRS _ DB (In_mpd_keep _ _ _ Hb))). }
    assert (DJD : forall A k, (A + k <= md_p d \/ md_p d + 4 * md_n d <= A) -> disjoint_from [(md_p d, md_p d + 4 * md_n d)] A k).
    { intros A k HA. cbn [disjoint_from]. split; [clear - HA; lia| exact I]. }
    assert (BLKD : forall B k, In (B, k) LBq -> (B, k) <> (md_p d, 4 * md_n d) -> 0 < k -> B + k <= md_p d \/ md_p d + 4 * md_n d <= B).
    { intros B k Hb NE Hk. pose proof (blocks_apart_neq _ _ _ BAq Hb IND NE ltac:(cbn; exact Hk) ltac:(cbn; clear - ND1; lia)) as K. cbn [fst snd] in K. clear - K. lia. }
    unfold cstateA.
    split; [exact HH2|]. split; [rewrite HT2, HS2, HF2; exact (conj HTc (conj HSc HFc))|]. split; [intros x Hx; exact (HCS2 x (HCSc x Hx))|].
    split; [split; [clear - HV2 HVc; lia| clear - HFR2 HFRc; lia]|].
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros dj Hdj. destruct (remove_nth_src _ _ _ Hdj) as (j & Hj & NE).
      pose proof (proj1 (Forall_forall _ _) LOK dj (nth_error_In _ _ Hj)) as (MJ & NSJ & JL & JA8 & OJ).
      assert (NEB : md_own dj = LHeap -> (md_p dj, 4 * md_n dj) <> (md_p d, 4 * md_n d)).
      { intros O E. injection E as E1 E2. exact (LA _ _ _ _ Hj Hi NE O OD E1). }
      destruct (mpd_step mq m2 hq h2 LBq LB2 LB2 SPc _ dj MJ OJ HP MI MI2 HCS2 ltac:(clear - LOS LOC; lia)
                  (loc_client _ _ _ JL (fun K => K))) as [MJ2 OJ2].
      - intros O. apply KEEP; [exact (proj1 (mpd_heap_in _ _ _ MJ O))| exact (NEB O)].
      - apply DJD. destruct (loc_vs_low _ _ _ JL PDC DBF) as [K|K]; [right; exact K| left; exact K].
      - intros O. apply DJD. destruct (mpd_heap_in _ _ _ MJ O) as [INJ NJ1].
        destruct (BLKD _ _ INJ (NEB O) ltac:(clear - NJ1; lia)) as [K|K]; [left; exact K| right; exact K].
      - intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. apply KEEP; [exact (proj1 (mpd_heap_in _ _ _ MJ O))| exact (NEB O)].
      - split; [exact MJ2|]. split; [exact NSJ|]. split; [exact JL|]. split; [exact JA8| exact OJ2]. }
    split; [apply structs_apart_remove; exact SA|]. split; [apply limbs_apart_remove; exact LA|].
    (* [comment removed for export] *)
    assert (NEW : md_own dW = LHeap -> (md_p dW, 4 * md_n dW) <> (md_p d, 4 * md_n d)).
    { intros O E. apply (proj1 (WB O)). rewrite E. exact DB. }
    destruct (mpd_step mq m2 hq h2 LBq LB2 LB2 SPc _ dW MW ltac:(rewrite WK1; exact OW) HP MI MI2 HCS2 ltac:(clear - LOS LOC; lia)
                ltac:(rewrite WK1; exact (w0_client_step _ SPc KS CSP))) as [MW2 OW2].
    { intros O. apply KEEP; [exact (proj1 (mpd_heap_in _ _ _ MW O))| exact (NEW O)]. }
    { apply DJD. rewrite WK1.
      pose proof (fresh_apart_client R KEEP0 LF lo W0 16 _ _ DFR w0_client ltac:(clear; lia) ltac:(clear - ND1; lia) ltac:(clear - ALO LOS; lia)) as AP.
      clear - AP. lia. }
    { intros O. apply DJD. destruct (mpd_heap_in _ _ _ MW O) as [INW NW1].
      destruct (BLKD _ _ INW (NEW O) ltac:(clear - NW1; lia)) as [K|K]; [left; exact K| right; exact K]. }
    { intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. apply KEEP; [exact (proj1 (mpd_heap_in _ _ _ MW O))| exact (NEW O)]. }
    split; [exact MW2|]. split; [rewrite <- WK1; exact OW2|].
    split.
    { (* [comment removed for export] *)
      split; [exact WK1|]. split; [exact WK2|]. split; [exact EP|]. split.
      - intros O. destruct (WB O) as (WNL & WOR). split; [| exact WOR]. intros HIn. apply WNL. exact (remove_nth_blk_in _ _ _ HIn).
      - intros b Hb0 Hb2. destruct (WK b Hb0 (BACK _ Hb2)) as [E|Hl]; [left; exact E| right].
        destruct (remove_nth_blk _ _ _ _ Hi Hl) as [K|K]; [| exact K].
        exfalso. destruct (mpd_blk_heap _ _ K) as [_ ->]. exact (NINf _ Hb2). }
    split.
    { intros b Hb NW. apply KEEP; [exact (SUB b Hb NW)|]. intros ->. exact (NW (FRS _ DB Hb)). }
    split.
    { intros b Hb. destruct (COV b (BACK _ Hb)) as [Hl|[Hf|Hw]]; [left; exact Hl| right; left| right; right; exact Hw].
      destruct (remove_nth_blk _ _ _ _ Hi Hf) as [K|K]; [| exact K].
      exfalso. destruct (mpd_blk_heap _ _ K) as [_ ->]. exact (NINf _ Hb). }
    split; [intros b Hb HL; exact (FRS _ (remove_nth_blk_in _ _ _ Hb) HL)|].
    split.
    { eapply (ext_step mq hq LBq ls dW CS SHC v f m2 h2 LB2 LB2 SPc _ CST' HP MI2 HCS2 ltac:(clear; lia) CSP KS KS).
      intros e He. destruct (fresh_vs_ext e _ _ He DFR ltac:(clear - ND1; lia)) as [X1 X2].
      split; [apply DJD; clear - X1; lia|]. intros O. apply DJD. specialize (X2 O). clear - X2. lia. }
    split.
    { eapply (pres_step mq m2 hq LB2 SPc _ PX HP HSc KS CSP). apply Forall_cons; [| apply Forall_nil]. right; right; left. cbn [fst snd].
      replace (md_p d + 4 * md_n d - md_p d) with (4 * md_n d) by (clear; lia). exact DFR. }
    split; [intros b Hb; exact (FRL _ (remove_nth_blk_in _ _ _ Hb))|].
    split; [exact FRW|]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { eapply (cells_step mq m2 hq LB2 SPc _ ls CS HP CH CHS).
      apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as [[[C1 C2]|[[C1 C2]|[C1 C2]]] C3].
      - split; [left; exact C1|]. apply DJD. right. clear - C1 PDC ALO LOS LOC. lia.
      - split; [right; clear - C1 C2 FN64; lia|]. apply DJD. clear - DBF C1 C2 FN64. lia.
      - split; [right; clear - C1 C2; lia|]. apply DJD. clear - DBF C1 C2. lia. }
    split.
    { apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as [CL C3]. split; [exact CL|]. intros d' Hd'. exact (C3 d' (In_remove_nth _ _ _ Hd')). }
    split; [| exact SHN].
    eapply (shadow_step mq m2 hq LB2 SPc _ SHC); [right| exact HP| exact SHD| exact SHN].
    intros x Hx. replace x with (FB + (x - FB)) by (clear; lia). eapply (hcs_fake segs R HIA hq _ _ mq FB FN HH); [left; reflexivity| clear - Hx; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="DIMG H0M LOS LOC CSP FRSH FN64 FB8 W0WR W0AS ESF"] Lemma cs_nop : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pm2,P,(12.&40.)(5.(12.&8.))PWX,(1.$4=.)P,(51.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(37.Vsegs,VR,VHIA,R;.R:.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R3.)P,(1:.Vsegs,VR,R;.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)VSPc,(1;.VR,)(39.Vsegs,VR,VHIA,R<.)R3.R=.R4.)P,(44.Vsegs,R5.)P,(45.Vsegs,R6.Vlo,VSPc,)P,(1>.(10.$11.$11.)Lw,(10.$11.$11.)(1?.(14.(16.$11.$11.R1.)(17.$11.$11.R1.))(1?.(;.(1?.(14.VSPc,(16.$11.$11.R1.))(14.(17.$11.$11.R1.)VSP,))(1?.(14.(15.VFB,+20.)(16.$11.$11.R1.))(14.(17.$11.$11.R1.)(36.(15.VFB,VFN,)+8.))))Pd,$2.P,(8.$2.R1.R?.)(;.(14.(17.$11.$11.R3.)(22.R2.))(14.(15.(22.R2.)+10.)(16.$11.$11.R3.)))))R6.)P,(1>.(10.$11.(1.$33.))Lac,(10.$11.(1.$33.))(4>.R8.(16.$11.(1.$33.)R1.)(34.(35.(17.$11.(1.$33.)R1.))))R<.)(51.R9.R11.R10.R?.R>.R=.R<.R;.R:.)")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f m2 WX CST HH2 HP MI2 ST2 HWX CSD.
    dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (_ & NSW & EA & _ & _ & _ & _ & HFW & ASW & _ & _).
    pose proof CST as CST'. dest_cs CST.
    assert (KS : forall b, In b KEEP0 -> In b LBq) by (intros b Hb; apply SUB; [eapply In_mpd_keep; exact Hb| exact (In_mpd_keep_not_blk_w _ _ _ Hb)]).
    (* [comment removed for export] *)
    assert (DJg : forall WY, Forall (fun w => fst w <= snd w /\ (((SPc <= fst w /\ snd w <= SP) \/ (FB + 32 <= fst w /\ snd w <= FB + FN - 8))
                     /\ forall d, In d ls -> snd w <= md_addr d \/ md_addr d + 16 <= fst w)) WY ->
                  forall A k, (A + k <= SPc /\ (A + k <= FB + 32 \/ FB + FN - 8 <= A)) \/ SP <= A -> disjoint_from WY A k).
    { intros WY HW. induction HW as [|w WY' [Hw1 Hw] _ IH]; intros A k HA; [exact I|]. destruct w as [a b]. cbn [fst snd] in Hw1, Hw. cbn [disjoint_from].
      split; [| exact (IH A k HA)].
      ddestruct Hw as [[[W1 W2]|[W1 W2]] _]; destruct HA as [[K1 K2]|K];
        [clear - W1 K1; lia| clear - W2 K; lia| clear - K2 W1 W2; lia| clear - W2 K F1 ALO LOS LOC CSP FN64; lia]. }
    pose proof (DJg WX HWX) as DJ.
    assert (DJLg : forall WY, Forall (fun w => fst w <= snd w /\ (((SPc <= fst w /\ snd w <= SP) \/ (FB + 32 <= fst w /\ snd w <= FB + FN - 8))
                     /\ forall d, In d ls -> snd w <= md_addr d \/ md_addr d + 16 <= fst w)) WY ->
                  forall d, In d ls -> disjoint_from WY (md_addr d) 16).
    { intros WY HW. induction HW as [|w WY' [Hw1 Hw] _ IH]; intros d Hd; [exact I|]. destruct w as [a b]. cbn [fst snd] in Hw1, Hw. cbn [disjoint_from].
      split; [| exact (IH d Hd)].
      destruct Hw as [_ W3]. destruct (W3 d Hd) as [K|K]; clear - K; lia. }
    pose proof (DJLg WX HWX) as DJL.
    assert (BLK : forall B k, In (B, k) LBq -> disjoint_from WX B k).
    { intros B k Hb. destruct (blk_facts _ _ _ _ _ HH Hb) as (_ & BC & BF). apply DJ. left. split; [clear - BC ALO LOS LOC; lia| clear - BF FN64; lia]. }
    unfold cstateA.
    split; [exact HH2|]. split; [exact (conj HTc (conj HSc HFc))|]. split; [exact HCSc|]. split; [exact (conj HVc HFRc)|].
    split.
    { apply Forall_forall. intros dj Hdj. pose proof (proj1 (Forall_forall _ _) LOK dj Hdj) as (MJ & NSJ & JL & JA8 & OJ).
      destruct (mpd_step mq m2 hq hq LBq LBq LBq SPc WX dj MJ OJ HP MI MI2 ltac:(intros x Hx; exact Hx) ltac:(clear - LOS LOC; lia)
                  (loc_client _ _ _ JL (fun K => K))) as [MJ2 OJ2].
      - intros O. exact (proj1 (mpd_heap_in _ _ _ MJ O)).
      - exact (DJL dj Hdj).
      - intros O. exact (BLK _ _ (proj1 (mpd_heap_in _ _ _ MJ O))).
      - intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. exact (proj1 (mpd_heap_in _ _ _ MJ O)).
      - split; [exact MJ2|]. split; [exact NSJ|]. split; [exact JL|]. split; [exact JA8| exact OJ2]. }
    split; [exact SA|]. split; [exact LA|].
    destruct (mpd_step mq m2 hq hq LBq LBq LBq SPc WX dW MW ltac:(rewrite EA; exact OW) HP MI MI2 ltac:(intros x Hx; exact Hx) ltac:(clear - LOS LOC; lia)
                ltac:(rewrite EA; exact (w0_client_step _ SPc KS CSP))) as [MW2 OW2].
    { intros O. exact (proj1 (mpd_heap_in _ _ _ MW O)). }
    { rewrite EA. apply DJ. destruct ASW as [K|K]; [left; split; [clear - K LOC; lia| clear - WFB FN64; lia]| right; exact K]. }
    { intros O. exact (BLK _ _ (proj1 (mpd_heap_in _ _ _ MW O))). }
    { intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. exact (proj1 (mpd_heap_in _ _ _ MW O)). }
    split; [exact MW2|]. split; [rewrite <- EA; exact OW2|]. split; [exact WOK|]. split; [exact SUB|]. split; [exact COV|]. split; [exact FRS|].
    split.
    { eapply (ext_step mq hq LBq ls dW CS SHC v f m2 hq LBq LBq SPc WX CST' HP MI2 ltac:(intros x Hx; exact Hx) ltac:(clear; lia) CSP KS KS).
      intros e He. destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (_ & _ & _ & _ & HFE & ASE & EFB).
      split; [apply DJ; destruct ASE as [K|K]; [left; split; [clear - K LOC; lia| clear - EFB FN64; lia]| right; exact K]|].
      intros O. exact (BLK _ _ (proj1 (HFE O))). }
    split.
    { eapply (pres_step mq m2 hq LBq SPc WX PX HP HSc KS CSP).
      apply Forall_forall. intros [a b] Hw. pose proof (proj1 (Forall_forall _ _) HWX _ Hw) as [Hw1 Hw2]. cbn [fst snd] in Hw1, Hw2.
      ddestruct Hw2 as [[[W1 W2]|[W1 W2]] _]; [right; right; right; cbn [fst snd]; clear - W1 W2 LOS LOC; lia| right; left; cbn [fst snd]; clear - W1 W2; lia]. }
    split; [exact FRL|]. split; [exact FRW|]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { eapply (cells_step mq m2 hq LBq SPc WX ls CS HP CH CHS).
      apply Forall_forall. intros ac Hac. split; [| exact (proj1 (Forall_forall _ _) CSD _ Hac)].
      pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as [[[C1 C2]|[[C1 C2]|[C1 C2]]] _]; [left; exact C1| right; clear - C1 C2 FN64; lia| right; clear - C1 C2; lia]. }
    split; [exact CHS|]. split; [| exact SHN].
    eapply (shadow_step mq m2 hq LBq SPc WX SHC); [left; exact HH| exact HP| exact SHD| exact SHN].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma cs_drop_null : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pi,$0.Pd,$2.P,(51.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(4.(5.$2.)(6.$2.R9.R3.)(7.$2.R2.))P,(4.$23.(24.R3.)$2:.)(51.R>.R=.R<.(<.$2.R5.R;.)R:.R9.R8.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f i d CST Hi OD. dest_cs CST. ddestruct WOK as (WK1 & WK2 & EP & WB & WK).
    assert (NB : forall b, In b (flat_map mpd_blk ls) -> In b (flat_map mpd_blk (remove_nth i ls))).
    { intros b Hb. destruct (remove_nth_blk _ _ _ _ Hi Hb) as [K|K]; [| exact K]. unfold mpd_blk in K. rewrite OD in K. destruct K. }
    unfold cstateA.
    split; [exact HH|]. split; [exact (conj HTc (conj HSc HFc))|]. split; [exact HCSc|]. split; [exact (conj HVc HFRc)|].
    split; [apply Forall_forall; intros dj Hdj; exact (proj1 (Forall_forall _ _) LOK dj (In_remove_nth _ _ _ Hdj))|].
    split; [apply structs_apart_remove; exact SA|]. split; [apply limbs_apart_remove; exact LA|].
    split; [exact MW|]. split; [exact OW|].
    split.
    { split; [exact WK1|]. split; [exact WK2|]. split; [exact EP|]. split.
      - intros O. destruct (WB O) as (WNL & WOR). split; [| exact WOR]. intros HIn. apply WNL. exact (remove_nth_blk_in _ _ _ HIn).
      - intros b Hb0 Hb2. destruct (WK b Hb0 Hb2) as [E|Hl]; [left; exact E| right; exact (NB _ Hl)]. }
    split; [exact SUB|].
    split; [intros b Hb; destruct (COV b Hb) as [Hl|[Hf|Hw]]; [left; exact Hl| right; left; exact (NB _ Hf)| right; right; exact Hw]|].
    split; [intros b Hb HL; exact (FRS _ (remove_nth_blk_in _ _ _ Hb) HL)|].
    split; [exact EXT|]. split; [exact PX|]. split; [intros b Hb; exact (FRL _ (remove_nth_blk_in _ _ _ Hb))|].
    split; [exact FRW|]. split; [exact MI|]. split; [exact ST|]. split; [exact CH|].
    split.
    { apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as [CL C3]. split; [exact CL|]. intros d' Hd'. exact (C3 d' (In_remove_nth _ _ _ Hd')). }
    split; [exact SHD| exact SHN].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="FB"] Lemma cnt24_mpd_blk : forall d, cnt24 (mpd_blk d) <= 1.
  Proof.
    intros d. unfold mpd_blk. destruct (md_own d); try (rewrite cnt24_nil; lia).
    pose proof (cnt24_cons_le (md_p d, 4 * md_n d) []) as C2. rewrite cnt24_nil in C2. exact (proj2 C2).
  Qed.

  #[using="FB"] Lemma cnt24_flat_blk : forall ls, cnt24 (flat_map mpd_blk ls) <= Z.of_nat (length ls).
  Proof.
    induction ls as [|d r IH]; [cbn [flat_map length]; rewrite cnt24_nil; lia|].
    cbn [flat_map length]. rewrite cnt24_app. pose proof (cnt24_mpd_blk d). lia.
  Qed.

  #[using="HND"] Lemma cs_cnt24 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.P,(51.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(14.(5<.R8.)(15.(15.(5<.VLB,)(34.(5=.$2.R7.)))+1.))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f CST. dest_cs CST.
    pose proof (HND _ _ _ _ HH) as ND. apply NoDup_map_inv in ND.
    assert (INC : incl LBq (LB ++ flat_map mpd_blk ls ++ mpd_blk dW)).
    { intros b Hb. apply in_or_app. destruct (COV b Hb) as [X|[X|X]]; [left; exact X| right; apply in_or_app; left; exact X| right; apply in_or_app; right; exact X]. }
    pose proof (cnt24_incl _ _ ND INC) as C. rewrite !cnt24_app in C.
    pose proof (cnt24_flat_blk ls). pose proof (cnt24_mpd_blk dW). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition wl_ok (d : mpd) (w : ivl) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "(;.(1?.(14.(22.O2.)(16.$11.$11.O1.))(14.(17.$11.$11.O1.)(15.(22.O2.)+10.)))(;.(1?.(4.$23.(24.O2.)$25.)(1?.(14.(26.O2.)(16.$11.$11.O1.))(14.(17.$11.$11.O1.)(15.(26.O2.)(27.+4.(28.O2.))))))(1?.(14.Vlo,(16.$11.$11.O1.))(14.(17.$11.$11.O1.)VSPc,))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma wl_outside : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pd,$2.PWX,(1.$4=.)Px,$11.P,(1>.$4=.(5>.R3.)R2.)P,(5?.(1<.(10.$11.$11.)(1=.$11.$11.(26.R4.)(15.(26.R4.)(27.+4.(28.R4.))))(1<.(10.$11.$11.)(1=.$11.$11.Vlo,VSPc,)(1<.(10.$11.$11.)(1=.$11.$11.(22.R4.)(15.(22.R4.)+10.))(42.(10.$11.$11.)))))R2.)(5?.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros d WX x HW HO. induction HW as [|[a b] WX' Hw _ IH]; [exact I|]. cbn [outside fst snd] in *.
    split; [| exact IH]. ddestruct HO as (O1 & O2 & O3 & _).
    destruct Hw as [[W1 W2]|[(_ & W1 & W2)|[W1 W2]]]; cbn [fst snd] in W1, W2; intros Hin; [apply O3| apply O1| apply O2]; clear - W1 W2 Hin; lia.
  Qed.

  #[using="HND DIMG H0M LOS LOC CSP SPT FRSH FN64 FB8 W0WR W0AS ESF"] Lemma cs_upd_l : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pi,$0.Pd,$2.Pd',$2.Pm2,P,(12.&40.)(5.(12.&8.))PWX,(1.$4=.)P,(51.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(4.(5.$2.)(6.$2.R<.R6.)(7.$2.R5.))P,(37.Vsegs,VR,VHIA,R?.R>.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R4.)P,(1:.Vsegs,VR,R?.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)VSPc,(1;.VR,)(39.Vsegs,VR,VHIA,R10.)R4.R11.R5.)P,(44.Vsegs,R6.)P,(45.Vsegs,R7.Vlo,VSPc,)P,(1>.$4=.(5>.R:.)R7.)P,(2;.Vsegs,R9.R13.R:.)P,(4.$11.(22.R;.)(22.R<.))P,(4.$23.(24.R<.)(24.R=.))P,(4.$11.(26.R=.)(26.R>.))P,(4.$11.(28.R>.)(28.R?.))(51.R>.R19.R18.(59.$2.R11.R17.R?.)R16.R15.R14.R13.R12.)")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f i d d' m2 WX CST Hi HH2 HP MI2 ST2 HWX MA2 EA EO EP EN.
    dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MD & NSD & _ & _ & _ & _ & HFD & _).
    pose proof CST as CST'. dest_cs CST'.
    assert (EB : mpd_blk d' = mpd_blk d) by (unfold mpd_blk; rewrite EO, EP, EN; reflexivity).
    replace v with (v + 0) by (clear; lia). replace f with (f + 0) by (clear; lia).
    eapply (cs_binop_l mq hq LBq ls dW CS SHC v f i d m2 hq LBq d' 0 0 CST Hi HH2); try reflexivity; try (intros x Hx; exact Hx); try (clear; lia); try assumption.
    - (* [comment removed for export] *)
      split; [exact EA|]. split; [rewrite EO; exact NSD|]. split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|].
      intros b _ _. exact EB.
    - (* [comment removed for export] *)
      assert (HBR : forall bk, In bk (mpd_keep LBq d ++ LF') -> fst bk + snd bk <= hl_ceil L).
      { intros bk Hbk. destruct (hm_apart segs R HIA hq LBq LF' mq HH) as [HBRq _]. rewrite Forall_forall in HBRq.
        assert (Hb' : In bk (LBq ++ LF')) by (apply in_app_iff in Hbk; apply in_app_iff; destruct Hbk as [K|K]; [left; eapply In_mpd_keep; exact K| right; exact K]).
        ddestruct (HBRq bk Hb') as (_ & _ & HC & _). exact HC. }
      assert (HPk : presA segs R (mpd_keep LBq d) LF' SPc (arl_stklo R) (hstkhi segs R HIA hq)
                      [(md_p d, md_p d + 4 * md_n d); (lo, SPc); (md_addr d, md_addr d + 16)] mq m2).
      { eapply presA_weaken; [exact HP| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. exact (wl_outside _ _ _ HWX Hx). }
      assert (HPk2 : presA segs R (mpd_keep LBq d) LF' SPc (arl_stklo R) (hstkhi segs R HIA hq) [(lo, SPc); (md_addr d, md_addr d + 16)] mq m2).
      { destruct (md_own d) eqn:EOD.
        - (* [comment removed for export] *)
          pose proof MD as [(_ & _ & _ & _ & _ & OWN) _]. rewrite EOD in OWN. destruct OWN as [P0 N0].
          eapply presA_weaken; [exact HPk| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
          intros x Hx. cbn [outside] in Hx |- *. split; [rewrite P0, N0; clear; lia| exact Hx].
        - ddestruct (HFD eq_refl) as (_ & _ & IND & ND1 & _).
          eapply (presA_drop_freed segs R HIA hq LBq LF' (mpd_keep LBq d) _ (md_p d) (4 * md_n d) mq mq m2 SPc HH IND);
            [| exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS LOC; lia| exact HPk].
          intros b x Hb _. split; [eapply In_mpd_keep; exact Hb|]. intros E. subst b.
          apply (In_mpd_keep_not_blk_w _ _ _ Hb). unfold mpd_blk. rewrite EOD. left. reflexivity.
        - exfalso. exact (NSD eq_refl). }
      eapply (presA_drop_below_w segs R HIA (mpd_keep LBq d) LF' _ lo SPc mq m2 SPc); [exact HBR| exact HPk2| clear; lia| exact LOS].
    - intros b Hb. left. rewrite <- EB. exact Hb.
    - intros b Hb. left. rewrite <- EB. exact Hb.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HND DIMG H0M LOS LOC CSP SPT FRSH FN64 FB8 W0WR W0AS ESF"] Lemma cs_upd_w : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.PdW',$2.Pm2,P,(12.&40.)(5.(12.&8.))P,(51.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(37.Vsegs,VR,VHIA,R;.R:.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R2.)P,(1:.Vsegs,VR,R;.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)VSPc,(1;.VR,)(39.Vsegs,VR,VHIA,R<.)(1<.(10.$11.$11.)(1=.$11.$11.(22.VdW0,)(15.(22.VdW0,)+10.))(42.(10.$11.$11.)))R=.R3.)P,(44.Vsegs,R4.)P,(45.Vsegs,R5.Vlo,VSPc,)P,(2;.Vsegs,R6.R>.R7.)P,(4.$11.(22.R8.)(22.VdW0,))P,(4.$23.(24.R9.)(24.R>.))P,(4.$11.(26.R:.)(26.R?.))P,(4.$11.(28.R;.)(28.R10.))P,(4.(12.&40.)(32.R<.)(32.R11.))(51.R<.R15.R14.R13.R=.R11.R10.R?.R>.)")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f dW' m2 CST HH2 HP MI2 ST2 MA2 EA EO EP EN EPD.
    dpose (mca_facts) as (LO0 & ALO & F0 & F1 & WFB).
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (_ & NSW & EAW & _ & _ & _ & _ & _ & _ & _ & OWq).
    pose proof CST as CST'. dest_cs CST'.
    assert (EB : mpd_blk dW' = mpd_blk dW) by (unfold mpd_blk; rewrite EO, EP, EN; reflexivity).
    assert (KS : forall b, In b KEEP0 -> In b LBq) by (intros b Hb; apply SUB; [eapply In_mpd_keep; exact Hb| exact (In_mpd_keep_not_blk_w _ _ _ Hb)]).
    replace v with (v + 0) by (clear; lia). replace f with (f + 0) by (clear; lia).
    eapply (cs_binop_w mq hq LBq ls dW CS SHC v f m2 hq LBq dW' 0 0 SPc CST HH2); try reflexivity; try (intros x Hx; exact Hx); try (clear; lia); try assumption.
    - eapply (presA_aobj segs R); [exact (hcs_ok segs R HIA hq)| exact HP| exact OWq| exact (w0_client_step _ SPc KS CSP)| clear - LOS LOC; lia| intros x Hx; eapply hcs_below_top; exact Hx].
    - split; [rewrite EA, EAW; reflexivity|]. split; [rewrite EO; exact NSW|]. split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|].
      intros b _ _. exact EB.
    - eapply presA_weaken; [exact HP| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx].
    - intros b Hb. left. rewrite <- EB. exact Hb.
    - intros b Hb. left. rewrite <- EB. exact Hb.
    - rewrite EN. clear. lia.
    - apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as [[[C1 C2]|[[C1 C2]|[C1 C2]]] _];
        [left; exact C1| right; clear - C1 C2 FN64; lia| right; clear - C1 C2; lia].
    - apply Forall_forall. intros dj _ K. exact K.
  Qed.

  (* [comment removed for export] *)
  #[using="HND DIMG H0M LOS LOC CSP SPT FRSH FN64 FB8 W0WR W0AS ESF"] Lemma cs_calloc_attach : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.Pi,$0.Pd,$2.Pm3,P,(12.&40.)(5.(12.&8.))Ph2,(4<.Vsegs,VR,VHIA,)PA,$11.Pn,$11.Pd',$2.Pdv,$11.Pdf,$11.P,(51.R12.R11.R10.R?.R>.R=.R<.R;.R:.)P,(4.(5.$2.)(6.$2.R10.R:.)(7.$2.R9.))P,(4.$23.(24.R:.)$2:.)P,(37.Vsegs,VR,VHIA,R9.(1<.(10.$11.$11.)(1=.$11.$11.R8.(27.+4.R7.))R13.)(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R:.)P,(4.$11.(38.Vsegs,VR,VHIA,R:.)(38.Vsegs,VR,VHIA,R15.))P,(4.$11.(39.Vsegs,VR,VHIA,R;.)(39.Vsegs,VR,VHIA,R16.))P,(4.$11.(3:.Vsegs,VR,VHIA,R<.)(3:.Vsegs,VR,VHIA,R17.))P,Px,$11.P,(31.Vsegs,VR,VHIA,R19.R1.)(31.Vsegs,VR,VHIA,R?.R2.)P,(14.(3;.Vsegs,VR,VHIA,R>.)(15.(3;.Vsegs,VR,VHIA,R19.)R:.))P,(14.(3<.Vsegs,VR,VHIA,R?.)(15.(3<.Vsegs,VR,VHIA,R1:.)R:.))P,(1:.Vsegs,VR,R1:.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)VSPc,(1;.VR,)(39.Vsegs,VR,VHIA,R1;.)(1<.(10.$11.$11.)(1=.$11.$11.(22.R12.)(15.(22.R12.)+10.))(42.(10.$11.$11.)))R1<.R11.)P,(44.Vsegs,R12.)P,(45.Vsegs,R13.Vlo,VSPc,)P,(43.VR,R1=.(1<.(10.$11.$11.)(1=.$11.$11.VFB,VFN,)VLF,)R12.(27.+4.R11.))P,(2;.Vsegs,R15.(1<.(10.$11.$11.)(1=.$11.$11.R13.(27.+4.R12.))R1>.)R11.)P,(4.$11.(22.R12.)(22.R17.))P,(4.$23.(24.R13.)$25.)P,(4.$11.(26.R14.)R16.)P,(4.$11.(28.R15.)R16.)(51.R1:.R19.(1<.(10.$11.$11.)(1=.$11.$11.R18.(27.+4.R17.))R23.)(59.$2.R1<.R22.R16.)R21.R20.R1?.(15.R1>.R15.)(15.R1=.R14.))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f i d m3 h2 A n d' dv df CST Hi ON HH2 HT2 HS2 HF2 HCS2 HV2 HFR2 HP MI3 ST3 FRA MA3 EA EO EP EN.
    pose proof (HND _ _ _ _ HH2) as ND2.
    assert (ANEW : ~ In (A, 4 * n) LBq).
    { intros C. cbn [map fst] in ND2. apply NoDup_cons_iff in ND2. destruct ND2 as [NI _]. apply NI. apply in_map_iff. exists (A, 4 * n). split; [reflexivity| exact C]. }
    assert (EB' : mpd_blk d' = [(A, 4 * n)]) by (unfold mpd_blk; rewrite EO, EP, EN; reflexivity).
    assert (EB : mpd_blk d = []) by (unfold mpd_blk; rewrite ON; reflexivity).
    eapply (cs_binop_l mq hq LBq ls dW CS SHC v f i d m3 h2 ((A, 4 * n) :: LBq) d' dv df CST Hi HH2); try assumption.
    - split; [exact EA|]. split; [rewrite EO; discriminate|]. rewrite EB, EB'.
      split; [intros b [<-|Hb]; [right; left; reflexivity| left; exact Hb]|]. split; [intros b Hb _; right; exact Hb|]. intros b [].
    - eapply presA_weaken; [exact HP| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx].
    - rewrite EB'. intros b [<-|[]]. right. exact ANEW.
    - rewrite EB'. intros b [<-|[]]. right. cbn [fst snd]. eapply fresh_apart_blocks_mono; [exact FRA| intros b Hb; eapply In_mpd_keep; exact Hb].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma cs_pres : ltac2:(CDefT.buildp (gd_tbl_A_mpi_client2 ()) "Pmq,P,(12.&40.)(5.(12.&8.))Phq,(4<.Vsegs,VR,VHIA,)PLBq,(1.$3.)Pls,(1.$2.)PdW,$2.PCS,(1.(10.$11.(1.$33.)))PSHC,(1.$33.)Pv,$11.Pf,$11.P,(51.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(1:.Vsegs,VR,(41.VLB,VdW0,)VLF,VSP,(1;.VR,)(39.Vsegs,VR,VHIA,Vh0,)(1<.(10.$11.$11.)(1=.$11.$11.(22.VdW0,)(15.(22.VdW0,)+10.))(42.(10.$11.$11.)))Vm0,R:.)")
(* [comment removed for export] *).
  Proof. intros mq hq LBq ls dW CS SHC v f CST. dest_cs CST. exact PX. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma cs_chunks_ok : forall mq hq LBq ls dW CS SHC v f, cstateA mq hq LBq ls dW CS SHC v f -> Forall (chunk_okA ls) CS.
  Proof. intros mq hq LBq ls dW CS SHC v f CST. dest_cs CST. exact CHS. Qed.

End MCA.
