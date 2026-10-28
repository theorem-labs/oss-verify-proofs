(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_addsub U_mpi_free.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MpiClientX () : Init.string Init.list := ["Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.USpec.MpiClient.cstate"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.snd"; "null_mpd"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "mpd_struct"; "mpd_cx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_free.mpi_free_LB"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_free.mpi_free_X"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.USpec.MpiClient.set_nth"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "Corelib.Init.Datatypes.nil"].


(* [comment removed for export] *)
Definition mpd_cx (d : mpd) : list (Z * list cell) :=
  match md_own d with LHeap => [(md_p d, [CB (4 * length (md_limbs d))%nat (u32s (md_limbs d))])] | _ => [] end.
Definition mpd_struct (d : mpd) : Z * list cell :=
  (md_addr d, mpi_cells (md_p d) (Z_to_bv 64 (md_sg d)) (md_n d) (md_pad d)).
Definition null_mpd (A : Z) (pad : word) : mpd := mkMPD A 1 0 0 [] pad LNull.

Section MCX.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable HI : heap_iface segs L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP segs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr segs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.
  Variables (h0 : HST segs L HI) (LB : list blk) (mo0 : Model) (m0 : mem) (SP lo SPc : Z) (dW0 : mpd) (es : list mpd).
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis LOC : lo <= SPc.
  Hypothesis CSP : SPc <= SP.
  Hypothesis SPT : SP <= heap_top segs L HI h0.
  Hypothesis SPB : SP < 2^64.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis W0NS : md_own dW0 <> LStatic.
  Hypothesis W0WR : mpd_writable L LB SP (heap_top segs L HI h0) dW0.
  Hypothesis W0AS : md_addr dW0 + 16 <= lo \/ SP <= md_addr dW0.
  Hypothesis W0A8 : md_addr dW0 mod 8 = 0.
  Hypothesis W0BLK : md_own dW0 = LHeap -> In (md_p dW0, 4 * md_n dW0) LB /\ 1 <= md_n dW0.
  Hypothesis ESF : ltac2:(CDefT.buildp (gd_tbl_MpiClientX ()) "(0.$1.Le,$1.(2.(3.VL,VLB,Vlo,(4.R1.)+10.)(2.P,(5.$6.(7.R1.)$8.)(9.(:.$;.$;.)(<.$;.$;.(=.R2.)(>.+4.(?.R2.)))VLB,)(2.(10.(11.(12.(4.R1.)+10.)Vlo,)(11.VSP,(4.R1.)))(2.P,(5.$6.(7.VdW0,)$8.)(10.(11.(12.(4.R2.)+10.)(=.VdW0,))(11.(12.(=.VdW0,)(>.+4.(?.VdW0,)))(4.R2.)))(2.(10.(13.(5.$6.(7.VdW0,)$8.))(10.(5.$6.(7.R1.)$14.)(10.(11.(12.(=.VdW0,)(>.+4.(?.VdW0,)))(=.R1.))(11.(12.(=.R1.)(>.+4.(?.R1.)))(=.VdW0,)))))(2.(10.(11.(12.(4.VdW0,)+10.)(4.R1.))(11.(12.(4.R1.)+10.)(4.VdW0,)))P,(13.(5.$6.(7.R1.)$14.))(10.(11.(12.(4.VdW0,)+10.)(=.R2.))(11.(12.(=.R2.)(>.+4.(?.R2.)))(4.VdW0,)))))))))Ves,)")
(* [comment removed for export] *).
  #[local] Set Default Proof Using "HLS DIMG HND IMGC SW ROIMG ACL LOC CSP SPT SPB DHI W0NS W0WR W0AS W0A8 W0BLK ESF".

  Notation CST := (cstate segs L HI h0 LB mo0 m0 SP lo SPc dW0 es).
  Local Ltac mcx H := exact (H segs L HI HLS DIMG HND IMGC SW ROIMG h0 LB mo0 m0 SP lo SPc dW0 es ACL LOC CSP SPT SPB DHI W0NS W0WR W0AS W0A8 W0BLK ESF).
  (* [comment removed for export] *)
  Local Ltac mcx' H := exact (H segs L HI HLS DIMG HND IMGC SW ROIMG h0 LB SP lo SPc dW0 es ACL LOC CSP SPT SPB DHI W0NS W0WR W0AS W0A8 W0BLK ESF).
  Definition x_w_facts := ltac:(mcx @cs_w_facts).
  Definition x_local_facts := ltac:(mcx @cs_local_facts).
  Definition x_binop_l := ltac:(mcx @cs_binop_l).
  Definition x_binop_w := ltac:(mcx @cs_binop_w).
  Definition x_mpd_at_heap_presx' := ltac:(mcx' @mpd_at_heap_presx').
  Definition x_statics_ok_heap_pres_ := ltac:(mcx' @statics_ok_heap_pres_).
  Ltac dest_cs H :=
    destruct H as (HH & HTc & MF & LOK & SA & LA & MW & WOK & EXOK & SUB & COV & FRS & EXT & PX & SOK & MI & ST & CH & CHS & CXH & CXS).

  (* [comment removed for export] *)
  Lemma cs_intro_local : ltac2:(CDefT.buildp (gd_tbl_MpiClientX ()) "Pmq,P,(15.&40.)(16.(15.&8.))Pmoq,$17.Phq,(18.Vsegs,VL,VHI,)PLBq,(19.$1:.)Pls,(19.$1.)PdW,$1.PEX,(19.$1:.)PCS,(19.(:.$;.(19.$1;.)))PCX,(19.(:.$;.(19.$1;.)))PA,$;.Ppad,(15.&40.)P,(1<.Vsegs,VL,VHI,Vh0,VLB,Vmo0,Vm0,VSP,Vlo,VSPc,VdW0,Ves,R;.R:.R9.R8.R7.R6.R5.(1=.(:.$;.(19.$1;.))(<.$;.(19.$1;.)R2.(1>.=(1?.&40.+1.)=R1.))R4.)R3.)P,(5.$;.(20.R3.+8.)=)P,(0.(:.$;.(19.$1;.))Lac,(:.$;.(19.$1;.))(10.(11.(12.(21.$;.(19.$1;.)R1.)(22.(23.(24.$;.(19.$1;.)R1.))))R5.)(11.(12.R5.+10.)(21.$;.(19.$1;.)R1.)))R6.)P,(0.$1.Ld,$1.(10.(11.(12.(4.R1.)+10.)R6.)(11.(12.R6.+10.)(4.R1.)))R:.)(1<.Vsegs,VL,VHI,Vh0,VLB,Vmo0,Vm0,VSP,Vlo,VSPc,VdW0,Ves,R?.R>.R=.R<.(1=.$1.(25.R6.R5.)R;.)R:.R9.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX A pad CST_ A8 APC APL. dest_cs CST_.
    pose proof (Forall_inv CH) as CHA. pose proof (Forall_inv CHS) as (A1 & A2 & _). cbn [fst snd] in CHA, A1, A2.
    assert (SZ : Z.of_nat (cells_size (mpi_cells 0 (Z_to_bv 64 1) 0 pad)) = 16) by reflexivity. rewrite SZ in A2.
    pose proof alloc_ceiling_pos as ACP.
    assert (FM : flat_map mpd_blk (null_mpd A pad :: ls) = flat_map mpd_blk ls) by reflexivity.
    split; [exact HH|]. split; [exact HTc|]. split; [exact MF|].
    split.
    { constructor; [| exact LOK]. split; [| cbn; split; [discriminate| split; [lia| split; [lia| exact A8]]]].
      split; [| cbn; left; reflexivity]. cbn. split; [exact CHA|]. split; [exact A8|]. split; [lia|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|]. auto. }
    split.
    { intros i j di dj Hi Hj NE. destruct i as [|i]; destruct j as [|j]; cbn in Hi, Hj; [congruence| | |].
      - injection Hi as <-. cbn [md_addr null_mpd]. pose proof (proj1 (Forall_forall _ _) APL dj (nth_error_In _ _ Hj)) as Q. cbn beta in Q. lia.
      - injection Hj as <-. cbn [md_addr null_mpd]. pose proof (proj1 (Forall_forall _ _) APL di (nth_error_In _ _ Hi)) as Q. cbn beta in Q. lia.
      - exact (SA i j di dj Hi Hj ltac:(congruence)). }
    split.
    { intros i j di dj Hi Hj NE Oi Oj. destruct i as [|i]; destruct j as [|j]; cbn in Hi, Hj; [congruence| | |].
      - injection Hi as <-. cbn in Oi. discriminate Oi.
      - injection Hj as <-. cbn in Oj. discriminate Oj.
      - exact (LA i j di dj Hi Hj ltac:(congruence) Oi Oj). }
    split; [exact MW|]. split; [unfold w_blk_ok in *; rewrite FM; exact WOK|].
    split. { apply Forall_forall. intros B HB. pose proof (proj1 (Forall_forall _ _) EXOK B HB) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; [change (flat_map mpd_blk (null_mpd A pad :: ls)) with (mpd_blk (null_mpd A pad) ++ flat_map mpd_blk ls); cbn [mpd_blk null_mpd md_own app]; exact X3| exact X4]. }
    split; [exact SUB|]. split; [rewrite FM; exact COV|]. split; [rewrite FM; exact FRS|]. split; [exact EXT|]. split; [exact PX|].
    split; [exact SOK|]. split; [exact MI|]. split; [exact ST|]. split; [exact (Forall_inv_tail CH)|].
    split.
    { apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) (Forall_inv_tail CHS) ac Hac) as (B1 & B2 & B3).
      split; [exact B1|]. split; [exact B2|]. intros d [<-|Hd]; [| exact (B3 d Hd)]. cbn. exact (proj1 (Forall_forall _ _) APC ac Hac). }
    split; [exact CXH| exact CXS].
  Qed.

  (* [comment removed for export] *)
  Lemma cs_drop_local : ltac2:(CDefT.buildp (gd_tbl_MpiClientX ()) "Pmq,P,(15.&40.)(16.(15.&8.))Pmoq,$17.Phq,(18.Vsegs,VL,VHI,)PLBq,(19.$1:.)Pls,(19.$1.)PdW,$1.PEX,(19.$1:.)PCS,(19.(:.$;.(19.$1;.)))PCX,(19.(:.$;.(19.$1;.)))Pd,$1.P,(1<.Vsegs,VL,VHI,Vh0,VLB,Vmo0,Vm0,VSP,Vlo,VSPc,VdW0,Ves,R:.R9.R8.R7.(1=.$1.R1.R6.)R5.R4.R3.R2.)(2.(1<.Vsegs,VL,VHI,Vh0,VLB,Vmo0,Vm0,VSP,Vlo,VSPc,VdW0,Ves,R;.R:.R9.R8.R7.R6.(26.$1:.R5.(27.R2.))(1=.(:.$;.(19.$1;.))(28.R2.)R4.)(26.(:.$;.(19.$1;.))R3.(29.R2.)))(2.(0.$1:.LB,$1:.(13.(9.$1:.R1.(27.R3.)))R5.)(2.(10.(5.$;.(2:.R2.)+1.)(5.$;.(2:.R2.)-1.))(2.(5.$;.(22.(2;.(15.&40.)(2<.R2.)))(?.R2.))(2.(2.(11.=(?.R2.))(11.(?.R2.)$2=.))(2.(11.VSPc,(4.R2.))(2.(11.(12.(4.R2.)+10.)VSP,)(2.(5.$;.(20.(4.R2.)+8.)=)(2.(13.(5.$6.(7.R2.)$2>.))(2.P,(5.$6.(7.R2.)$14.)(2.(5.$;.(=.R3.)=)(5.$;.(?.R3.)=))P,(5.$6.(7.R2.)$8.)(2.(9.(:.$;.$;.)(<.$;.$;.(=.R3.)(>.+4.(?.R3.)))R9.)(2.(11.+1.(?.R3.))(2.(2?.=(=.R3.))(2.(11.(12.(=.R3.)(>.+4.(?.R3.)))(30.VL,))(2.(5.$;.(20.(=.R3.)+10.)=)P,(9.(:.$;.$;.)(<.$;.$;.(=.R3.)(>.+4.(?.R3.)))VLB,)(9.(:.$;.$;.)(<.$;.$;.(=.R4.)(>.+4.(?.R4.)))(27.VdW0,)))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX d CST_.
    destruct (cs_local_facts segs L HI HLS DIMG HND IMGC SW ROIMG h0 LB mo0 m0 SP lo SPc dW0 es ACL LOC CSP SPT SPB DHI W0NS W0WR W0AS W0A8 W0BLK ESF
                _ _ _ _ _ _ _ _ _ 0 d CST_ eq_refl) as (MD & NS & _ & _ & _ & _ & HFD & A1 & A2 & A8).
    dest_cs CST_. pose proof alloc_ceiling_pos as ACP.
    pose proof MD as [(HR & HAL & HPOS & HL & HN & HO) HS].
    assert (FM : flat_map mpd_blk (d :: ls) = mpd_blk d ++ flat_map mpd_blk ls) by reflexivity.
    assert (SUBL : forall b, In b (flat_map mpd_blk ls) -> In b (flat_map mpd_blk (d :: ls))) by (intros b Hb; rewrite FM; apply in_or_app; right; exact Hb).
    assert (SUBD : forall b, In b (mpd_blk d) -> In b (flat_map mpd_blk (d :: ls))) by (intros b Hb; rewrite FM; apply in_or_app; left; exact Hb).
    (* [comment removed for export] *)
    assert (DNL : forall b, In b (mpd_blk d) -> ~ In b (flat_map mpd_blk ls)).
    { intros b Hb Hl. destruct (mpd_blk_heap _ _ Hb) as [OD ->]. apply flat_map_blk_in in Hl. destruct Hl as (dj & Hdj & Oj & E).
      destruct (In_nth_error _ _ Hdj) as [j Hj]. injection E as E1 E2. exact (LA 0%nat (S j) d dj eq_refl Hj ltac:(discriminate) OD Oj E1). }
    split; [| split; [| split; [exact HS| split; [exact HL| split; [exact HN| split; [exact A1| split; [exact A2| split; [exact A8| split; [exact NS| split]]]]]]]]].
    2:{ apply Forall_forall. intros B HB Hb. pose proof (proj1 (Forall_forall _ _) EXOK B HB) as (_ & _ & X3 & _). exact (X3 (SUBD _ Hb)). }
    2:{ intros O. rewrite O in HO. exact HO. }
    2:{ intros O. destruct (HFD O) as (P0 & P4 & IN & N1 & FR). pose proof HO as HO'. rewrite O in HO'. destruct HO' as (_ & _ & PAL & _). repeat (split; [assumption|]). exact FR. }
    split; [exact HH|]. split; [exact HTc|]. split; [exact MF|].
    split; [exact (Forall_inv_tail LOK)|].
    split; [intros i j di dj Hi Hj NE; exact (SA (S i) (S j) di dj Hi Hj ltac:(congruence))|].
    split; [intros i j di dj Hi Hj NE; exact (LA (S i) (S j) di dj Hi Hj ltac:(congruence))|].
    split; [exact MW|].
    split.
    { destruct WOK as (X1 & X2 & X3 & WB & WK). split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split.
      - intros OW. destruct (WB OW) as (N1 & N2 & N3). split; [intros C; exact (N1 (SUBL _ C))|]. split; [| exact N3].
        intros C. apply in_app_or in C. destruct C as [C|C]; [exact (N2 C)| exact (N1 (SUBD _ C))].
      - intros b Hb0 Hbq. destruct (WK b Hb0 Hbq) as [E|[Hl|He]]; [left; exact E| | right; right; apply in_or_app; left; exact He].
        rewrite FM in Hl. apply in_app_or in Hl. destruct Hl as [Hl|Hl]; [right; right; apply in_or_app; right; exact Hl| right; left; exact Hl]. }
    split.
    { apply Forall_forall. intros B HB. apply in_app_or in HB. destruct HB as [HB|HB].
      - pose proof (proj1 (Forall_forall _ _) EXOK B HB) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; [intros C; exact (X3 (SUBL _ C))| exact X4].
      - destruct (mpd_blk_heap _ _ HB) as [OD ->]. destruct (HFD OD) as (P0 & P4 & IN & N1 & FR).
        split; [exact IN|]. split; [intros HL'; apply FRS; [exact (SUBD _ HB)| exact HL']|]. split; [exact (DNL _ HB)| cbn; lia]. }
    split; [exact SUB|].
    split.
    { intros b Hb. destruct (COV b Hb) as [X|[X|[X|X]]]; [left; exact X| | right; right; left; exact X| right; right; right; apply in_or_app; left; exact X].
      rewrite FM in X. apply in_app_or in X. destruct X as [X|X]; [right; right; right; apply in_or_app; right; exact X| right; left; exact X]. }
    split; [intros b Hb HL'; exact (FRS b (SUBL _ Hb) HL')|].
    split; [exact EXT|]. split; [exact PX|]. split; [exact SOK|]. split; [exact MI|]. split; [exact ST|].
    split; [constructor; [exact HR| exact CH]|].
    split.
    { constructor.
      - cbn [fst snd mpd_struct]. assert (SZ : Z.of_nat (cells_size (mpi_cells (md_p d) (Z_to_bv 64 (md_sg d)) (md_n d) (md_pad d))) = 16) by reflexivity.
        rewrite SZ. split; [exact A1|]. split; [exact A2|]. intros dj Hdj. destruct (In_nth_error _ _ Hdj) as [j Hj].
        pose proof (SA 0%nat (S j) d dj eq_refl Hj ltac:(discriminate)). lia.
      - apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) CHS ac Hac) as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
        intros dj Hdj. apply B3. right. exact Hdj. }
    split.
    { apply Forall_app. split; [exact CXH|]. unfold mpd_cx. destruct (md_own d) eqn:OD; [constructor| | constructor].
      constructor; [| constructor]. cbn [fst snd]. destruct HO as (_ & _ & _ & U). apply u32arr_cells. exact U. }
    apply Forall_app. split.
    - apply Forall_forall. intros ac Hac. destruct (proj1 (Forall_forall _ _) CXS ac Hac) as (B & HB & B1 & B2). exists B. split; [apply in_or_app; left; exact HB| exact (conj B1 B2)].
    - unfold mpd_cx, mpd_blk. destruct (md_own d) eqn:OD; [constructor| | constructor]. constructor; [| constructor]. cbn [fst snd].
      exists (md_p d, 4 * md_n d). split; [apply in_or_app; right; left; reflexivity|]. cbn [fst snd cells_size csize Nat.add]. rewrite <- HL. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_heap_nop0 : ltac2:(CDefT.buildp (gd_tbl_MpiClientX ()) "Pmq,P,(15.&40.)(16.(15.&8.))Pmoq,$17.Phq,(18.Vsegs,VL,VHI,)PLBq,(19.$1:.)Pls,(19.$1.)PdW,$1.PEX,(19.$1:.)PCS,(19.(:.$;.(19.$1;.)))PCX,(19.(:.$;.(19.$1;.)))Pm2,P,(15.&40.)(16.(15.&8.))Pmo2,$17.Ph2,(18.Vsegs,VL,VHI,)P,(1<.Vsegs,VL,VHI,Vh0,VLB,Vmo0,Vm0,VSP,Vlo,VSPc,VdW0,Ves,R<.R;.R:.R9.R8.R7.R6.R5.R4.)P,(31.Vsegs,VL,VHI,R2.R:.R4.R3.)P,(5.$;.(32.Vsegs,VL,VHI,R3.)(32.Vsegs,VL,VHI,R<.))P,(33.R>.R5.)P,(34.Vsegs,VL,R=.VSPc,R10.R7.)P,(35.Vsegs,R8.)P,(36.Vsegs,R9.Vlo,VSPc,)(1<.Vsegs,VL,VHI,Vh0,VLB,Vmo0,Vm0,VSP,Vlo,VSPc,VdW0,Ves,R:.R9.R8.R10.R?.R>.R=.R<.R;.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX m2 mo2 h2 CST_ HH2 HT2 MF2 PR MI2 ST2.
    destruct (x_w_facts _ _ _ _ _ _ _ _ _ CST_) as (MWf & NSW & EA & _ & LW & CRW & CRWL & HFW & ASW & WA8).
    pose proof CST_ as CST'. dest_cs CST_.
    eapply (x_binop_w mq moq hq LBq ls dW EX CS CX m2 mo2 h2 LBq dW);
      [exact CST'| exact HH2| exact HT2| exact MF2| | apply mpd_out_refl; exact NSW| apply heap_presx_of_pres; exact PR
      | eapply x_statics_ok_heap_pres_; [exact SOK| exact PR]| exact MI2| exact ST2| intros b Hb; left; exact Hb| reflexivity| lia].
    eapply (x_mpd_at_heap_presx' mq m2 LBq LBq LBq SPc []); [exact MWf| apply heap_presx_of_pres; exact PR| exact MI| exact MI2| | | cbn; exact I| intros _; cbn; exact I|].
    - intros a Ha. destruct (CRW a Ha) as [C|[C|C]]; [left; destruct ASW; lia| right; left; exact C| right; right; exact C].
    - intros O. destruct (HFW O) as (_ & _ & IN & _). eapply client_range_blk; [exact IN| lia| lia].
    - intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. destruct (HFW O) as (_ & _ & IN & _). exact IN.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_free_local : ltac2:(CDefT.buildp (gd_tbl_MpiClientX ()) "Pmq,P,(15.&40.)(16.(15.&8.))Pmoq,$17.Phq,(18.Vsegs,VL,VHI,)PLBq,(19.$1:.)Pls,(19.$1.)PdW,$1.PEX,(19.$1:.)PCS,(19.(:.$;.(19.$1;.)))PCX,(19.(:.$;.(19.$1;.)))Pi,$37.Pd,$1.Pm2,P,(15.&40.)(16.(15.&8.))Pmo2,$17.Ph2,(18.Vsegs,VL,VHI,)Ppad',(15.&40.)P,(1<.Vsegs,VL,VHI,Vh0,VLB,Vmo0,Vm0,VSP,Vlo,VSPc,VdW0,Ves,R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(5.(16.$1.)(38.$1.R<.R7.)(39.$1.R6.))P,(31.Vsegs,VL,VHI,R4.(3:.(7.R7.)(=.R7.)(?.R7.)R>.)R6.R5.)P,(5.$;.(32.Vsegs,VL,VHI,R5.)(32.Vsegs,VL,VHI,R10.))P,(33.R12.R7.)P,(3;.Vsegs,VL,(3:.(7.R:.)(=.R:.)(?.R:.)R11.)VSPc,(1=.(:.$;.$;.)(<.$;.$;.(4.R:.)(12.(4.R:.)+10.))(3<.(7.R:.)(=.R:.)(?.R:.)))R14.R9.)P,(3=.Vsegs,VL,R:.)P,(35.Vsegs,R;.)P,(36.Vsegs,R<.Vlo,VSPc,)P,(3>.Vsegs,R=.(4.R>.)(1>.=(1?.&40.+1.)=R:.))(1<.Vsegs,VL,VHI,Vh0,VLB,Vmo0,Vm0,VSP,Vlo,VSPc,VdW0,Ves,R>.R=.R<.(3:.(7.R?.)(=.R?.)(?.R?.)R16.)(3?.$1.R10.R15.(40.(4.R?.)+1.==(41.(15.&40.))R;.$14.))R14.R13.R12.R11.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX i d m2 mo2 h2 pad' CST_ Hi HH2 HT2 MF2 PX2 SOK2 MI2 ST2 STR.
    destruct (x_local_facts _ _ _ _ _ _ _ _ _ i d CST_ Hi) as (MD & NS & _ & _ & _ & _ & HFD & A1 & A2 & A8).
    pose proof CST_ as CST'. dest_cs CST_.
    pose proof (HND _ _ _ _ HH) as NDq. pose proof MD as [(_ & HAL & HPOS & _) _].
    assert (MD2 : mpd_at segs m2 (mpi_free_LB (md_own d) (md_p d) (md_n d) LBq) (mkMPD (md_addr d) 1 0 0 [] pad' LNull)).
    { split; [| cbn; left; reflexivity]. cbn. split; [exact STR|]. split; [exact HAL|]. split; [exact HPOS|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|]. split; reflexivity. }
    destruct (md_own d) eqn:OD; [| | exfalso; exact (NS eq_refl)].
    - (* [comment removed for export] *)
      cbn [mpi_free_LB mpi_free_X] in *.
      eapply (x_binop_l mq moq hq LBq ls dW EX CS CX i d m2 mo2 h2 LBq); [exact CST'| exact Hi| exact HH2| exact HT2| exact MF2| exact MD2| | | exact SOK2| exact MI2| exact ST2| cbn; intros b []].
      + split; [reflexivity|]. split; [cbn; discriminate|]. unfold mpd_blk. rewrite OD. cbn.
        split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|]. intros b [].
      + unfold mpd_ivs. rewrite OD. exact PX2.
    - cbn [mpi_free_LB mpi_free_X] in *.
      destruct (HFD eq_refl) as (PD0 & PD4 & IND & ND1 & _).
      set (LB2 := lb_remove (md_p d) LBq) in *.
      assert (NINf : forall k, ~ In (md_p d, k) LB2) by (intros k; subst LB2; apply lb_remove_notin; exact NDq).
      assert (KEEP : forall b, In b LBq -> b <> (md_p d, 4 * md_n d) -> In b LB2).
      { intros [B k] Hb NE. subst LB2. apply In_lb_remove_keep; [exact Hb|]. exact (nodup_fst_neq _ _ _ _ _ NDq IND Hb NE). }
      eapply (x_binop_l mq moq hq LBq ls dW EX CS CX i d m2 mo2 h2 LB2); [exact CST'| exact Hi| exact HH2| exact HT2| exact MF2| exact MD2| | | exact SOK2| exact MI2| exact ST2| cbn; intros b []].
      + split; [reflexivity|]. split; [cbn; discriminate|]. unfold mpd_blk. rewrite OD. cbn.
        split; [intros b Hb; left; subst LB2; eapply In_lb_remove; exact Hb|].
        split; [intros b Hb NB; apply KEEP; [exact Hb| intros ->; apply NB; left; reflexivity]|].
        intros b [<-|[]] Hb2. exfalso. exact (NINf _ Hb2).
      + unfold mpd_ivs. rewrite OD. intros a Ha Hc Ho. cbn in Ho. apply PX2; [exact Ha| | cbn; tauto].
        destruct Hc as [C|[C|([B k] & Hb & R)]]; [left; exact C| right; left; exact C| right; right]. cbn in R.
        exists (B, k). split; [| exact R]. apply KEEP; [exact Hb|]. intros E. injection E as -> ->. lia.
  Qed.
End MCX.
