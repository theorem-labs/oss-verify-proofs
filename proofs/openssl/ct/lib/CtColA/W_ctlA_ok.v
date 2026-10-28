(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA Fr_asn1_check_tlen W_check_tlenA W_get_object_closedA W_err_newA W_err_set_debugA W_err_vsetA ApErrKitA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import CtSizes CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColP Require W_check_tlen_gen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA W_check_tlen_genA W_ctlA_defs W_ctlA_exit W_ctlA_raise.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Import CtRepP.W_get_object(land_32_cases, go_ret_cases, go_cls_cases, go_tag_range).
Import CtRepP.W_get_object_walk(signed_small, zxb_lit).

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Act.
  Hypothesis STRCPY : strcpy_icontract RT.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m3 : mem) (Σ Σ1 : rts RT) (OW LB K : list block) (E : ap_env) (lo : Z) (ras : list Z).
  Variables (D : Z) (d : list Z) (op len PIC PPC : Z) (TLCo ot : option Z) (f spa : Z) (gg : nat) (junk gj : list byte) (bd bt : block) (qp ql qt qc : bptr).
  Hypothesis FACTS : ctl_factsA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m3 Σ Σ1 OW LB K E lo ras D d op len PIC PPC TLCo ot f spa gg junk gj bd bt.
  Local Notation pbs := (actl_pbs f qp ql qt qc).
  Local Notation XX := (ctl_XX PIC PPC TLCo).
  Local Notation memA := (ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc).
  Local Notation g := (get_object d op len).
  Variables (j0 j8 j16 j24 j32 j40 j128 j136 : list byte).
  Local Notation frame := (ctl_frameA j0 j8 j16 j24 j32 j40 f PIC PPC len ot j128 j136 gg junk).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ctl_finA : forall {A} (t : aprog bptr A) (Q : A -> rts RT -> machine_state -> Prop)
      (x1 x5 x11 x12 x14 x16 x20 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (ma : mem) (Σ4 : rts RT) (st4 : ap_st bptr) (OW4 : list block) (bo4 : Z * Z) (spent : Z) (bi bc : bv 8) (jl : list byte),
    go_err g = None ->
    memA ma Σ4 st4 OW4 bo4 spent frame ->
    rw_cells ctasegs ma PIC [C1 bi; C1 bc; CB 8 jl] -> rw_cells ctasegs ma PPC [C8 (Z_to_bv 64 (D + op))] -> ctl_tlcA TLCo ma ->
    rw_cells ctasegs ma (f + 64) [C8 (Z_to_bv 64 (go_len g))] -> rw_cells ctasegs ma (f + 96) [C8 (Z_to_bv 64 (D + go_p g))] ->
    (forall Σ' ms', ctl_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K spent PIC PPC TLCo 1
                      [C1 (Z_to_bv 8 (Z.land (go_ret g) 1)); C1 (Z_to_bv 8 (Z.land (go_ret g) 32)); C8 (wz (tlen_plen g op len))] (D + go_p g) st4 Σ' ms' ->
                    implAp t Σ' Q ms') ->
    implAp t Σ4 Q (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 (Z_to_bv 64 0) (Z_to_bv 64 PPC) sp (Z_to_bv 64 spa)
                        (Z_to_bv 64 (go_ret g)) x11 x12 (Z_to_bv 64 len) x14 (Z_to_bv 64 (D + op)) x16 (Z_to_bv 64 0)
                        (Z_to_bv 64 f) (Z_to_bv 64 (ctl_tlc TLCo)) x20 (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) (Z_to_bv 64 (f + 64)) x25 x26 (Z_to_bv 64 SHB) x28 x29 x30 x31)
                   F (Z_to_bv 64 0x242ad8) fc None ma (seg_rom ctasegs)).
  Proof.
    intros until jl. intros EG MEM HPIC HPPC HTLC OL OP HK. ctl_facts FACTS.
    pose proof MEM as (PRE4 & KEPT4 & AX4 & CRED4 & FRL & FRH). unfold ctl_frameA in FRL.
    pose proof PRE4 as (HEAP4 & _ & _ & _ & ST4 & _ & _ & _ & _ & MI4 & _ & _). rewrite ESPA in ST4.
    pose proof (get_object_bounds d op len ltac:(eapply Forall_impl; [| exact PF]; cbv beta; intros; lia) TL0) as GB. cbv zeta in GB. rewrite EG in GB.
    destruct GB as (GB1 & GB2 & GB3).
    pose proof (go_ret_cases d op len) as RC. cbv zeta in RC.
    assert (RB : 0 <= go_ret g < 64) by (destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER; clear; lia).
    assert (FLO : f + 128 <= spa) by (clear - G3 CEIL LOSP SPAL; plia).
    assert (EPPC : bv_unsigned (Z_to_bv 64 PPC) = PPC) by (apply unsigned_lit; clear - PPClo SPR PPChi; unfold USTACK_TOP in *; lia).
    assert (EPIC : bv_unsigned (Z_to_bv 64 PIC) = PIC) by (apply unsigned_lit; clear - PIClo SPR PIChi; unfold USTACK_TOP in *; lia).
    (* [comment removed for export] *)
    assert (HQL : In (ql, f + 64, 8) (OW4 ++ pbs ++ LB)) by (apply in_or_app; right; apply in_or_app; left; unfold actl_pbs; cbn; tauto).
    (* [comment removed for export] *)
    assert (FIN : forall (y12 y13 y14 : word) mb,
      memA mb Σ4 st4 OW4 bo4 spent frame ->
      rw_cells ctasegs mb PIC [C1 bi; C1 bc; CB 8 jl] -> rw_cells ctasegs mb PPC [C8 (Z_to_bv 64 (D + op))] -> ctl_tlcA TLCo mb ->
      rw_cells ctasegs mb (f + 64) [C8 (Z_to_bv 64 (tlen_plen g op len))] -> rw_cells ctasegs mb (f + 96) [C8 (Z_to_bv 64 (D + go_p g))] ->
      implAp t Σ4 Q (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 (Z_to_bv 64 0) (Z_to_bv 64 PPC) sp (Z_to_bv 64 spa)
                          (Z_to_bv 64 (go_ret g)) (Z_to_bv 64 (Z.land (go_ret g) 1)) y12 y13 y14 (Z_to_bv 64 (D + op)) x16 (Z_to_bv 64 0)
                          (Z_to_bv 64 f) (Z_to_bv 64 (ctl_tlc TLCo)) x20 (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) (Z_to_bv 64 (f + 64)) x25 x26 (Z_to_bv 64 SHB) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x242af8) fc None mb (seg_rom ctasegs))).
    { intros y12 y13 y14 mb MEMb HPICb HPPCb HTLCb OLb OPb. clear MEM PRE4 KEPT4 AX4 CRED4 FRL FRH HEAP4 ST4 MI4 HPIC HPPC HTLC OL OP.
      pose proof MEMb as (PREb & KEPTb & AXb & CREDb & FRL & FRH). unfold ctl_frameA in FRL.
      pose proof PREb as (HEAPb & _ & _ & _ & STb & _ & _ & _ & _ & MIb & _ & _). rewrite ESPA in STb.
      (* [comment removed for export] *)
      pose proof PIChi as PIChiN. pose proof PPChi as PPChiN. unfold USTACK_TOP in PIChiN, PPChiN.
      assert (ACCI : acc ctasegs mb PIC 10).
      { destruct HEAPb as (HAb & HSb & _). apply (af_acc_stack RT AF Σ4 mb _ _ HAb); [| clear - PIChi; lia].
        rewrite HSb. cbn [ar_SP0 push amb]. unfold BnHeapA.ACEIL in CEIL. clear - CEIL LOSP PIClo. lia. }
      assert (ACCP : acc ctasegs mb PPC 8).
      { destruct HEAPb as (HAb & HSb & _). apply (af_acc_stack RT AF Σ4 mb _ _ HAb); [| clear - PPChi; lia].
        rewrite HSb. cbn [ar_SP0 push amb]. unfold BnHeapA.ACEIL in CEIL. clear - CEIL LOSP PPClo. lia. }
      pose proof (munch_refl [(PIC, PIC + 10); (PPC, PPC + 8)]%Z mb) as MU. pose proof (wmono_refl ctasegs mb) as WM.
      assert (OFF : offshW [(PIC, PIC + 10); (PPC, PPC + 8)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - CN CEIL LOSP PIClo PPClo; plia).
      cut_hd HPICb HINF (PIC + 1). cut_hd HPICb HCST (PIC + 2). rename HPICb into HOLEN.
      apply implAp_from_evt.
      (* [comment removed for export] *)
      step. step.
      step. if_cases KI; zc KI; [exfalso; rewrite ?EPIC in KI; clear - KI PIClo LOSP LO0 CEIL CN; plia|]. clear KI.
      step. rewrite le1_lit. mem_after_store.
      (* [comment removed for export] *)
      step. if_cases KS; zc KS; [exfalso; revert KS; rewrite ?unsigned_lit by (clear - PIClo SPR PIChi; unfold USTACK_TOP in *; lia); clear - PIClo LO0 CEIL LOSP CN; plia|].
      step. setreg 10%Z (Z_to_bv 64 (Z.land (go_ret g) 32)) ltac:(rewrite ?(unsigned_lit (go_ret g)) by (clear - RB; lia); reflexivity).
      step. rewrite le1_lit. mem_after_store.
      (* [comment removed for export] *)
      step.
      step. if_cases KO; zc KO; [exfalso; revert KO; rewrite ?unsigned_lit by (clear - PIClo SPR PIChi; unfold USTACK_TOP in *; lia); clear - PIClo LO0 CEIL LOSP CN; plia|].
      step. step.
      (* [comment removed for export] *)
      step. if_true. step. if_true.
      step. step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mk end.
      match goal with H : munch _ mb mk |- _ => rename H into MUk end. match goal with H : wmono ctasegs mb mk |- _ => rename H into WMk end.
      match goal with H : stk ctasegs mk _ _ |- _ => rename H into STk end. match goal with H : mem_inv ctasegs mk |- _ => rename H into MIk end.
      apply evt_done.
      assert (MEMk : memA mk Σ4 st4 OW4 bo4 spent frame).
      { eapply (ctl_memA_munch ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc mb mk); [exact MEMb| exact MUk| exact WMk| exact MIk| exact STk| | | | | | exact ESPA].
        - constructor; [left; cbn [fst snd]; clear - CEIL LOSP PIClo PIChi; plia|]. constructor; [left; cbn [fst snd]; clear - CEIL LOSP PPClo PPChi; plia| constructor].
        - intros a HL. pose proof (@lib_addr_lowA (push AR f 1) _ _ _ _ a HEAPb HL) as Ha. cbn [outside fst snd]. clear - Ha CEIL LOSP PIClo PPClo. plia.
        - intros a [HX _]. unfold ctl_XX, LIBW_A in HX. cbn [rin_ivs fst snd app] in HX. cbn [outside fst snd]. clear - HX. lia.
        - intros a Ha. rewrite ctl_frameA_size in Ha. cbn [outside fst snd]. clear - Ha GSZ SPAH PIClo PPClo. lia.
        - intros a [_ Ha]. cbn [outside fst snd]. clear - Ha PIClo PPClo. lia. }
      (* [comment removed for export] *)
      join2 HINF HCST. join2 HINF HOLEN.
      eapply (ctl_exitA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS t Q);
        [exact MEMk| exact HINF| reflexivity| | | exact HK].
      - match goal with H : rw_cells ctasegs mk PPC [C8 ?v] |- _ =>
          replace v with (Z_to_bv 64 (D + go_p g)) in H; [exact H|] end.
        reflexivity.
      - destruct TLCo as [a|]; [| exact I]. destruct HTLCb as (vb & j & H). exists vb, j.
        destruct TB as (HBT & TB1 & TB2 & _).
        pose proof (@AH_range_gen (push AR f 1) _ _ _ _ bt HEAPb ltac:(apply in_or_app; right; apply in_or_app; right; exact HBT)) as (_ & _ & _ & BT3 & _).
        change (@BnHeapA.ACEIL (push AR f 1)) with (@BnHeapA.ACEIL AR) in BT3.
        eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MUk)| exact H|].
        intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside fst snd]. clear - Hx BT3 TB2 CEIL LOSP PIClo PPClo. plia. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(f + 64, f + 72)]%Z ma) as MU. pose proof (wmono_refl ctasegs ma) as WM.
    apply implAp_from_evt.
    step. setreg 11%Z (Z_to_bv 64 (Z.land (go_ret g) 1)) ltac:(rewrite (unsigned_lit (go_ret g)) by (clear - RB; lia); reflexivity).
    step. if_cases KI; zc KI.
    - (* [comment removed for export] *)
      assert (EPL : tlen_plen g op len = go_len g).
      { unfold CtColP.W_check_tlen_gen.tlen_plen. destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER in KI |- *; first [reflexivity| discriminate KI]. }
      apply evt_done. eapply FIN; [exact MEM| exact HPIC| exact HPPC| exact HTLC| rewrite EPL; exact OL| exact OP].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      step. zstep. unfold MallocRep.wz. rewrite ?(unsigned_lit (D + op)) by (clear - D0 OP0 OPT D63 TL0; lia). rewrite ?(unsigned_lit (D + go_p g)) by (clear - D0 GB1 GB3 OP0 OPT D63 TL0; lia).
      step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mb end.
      match goal with H : munch _ ma mb |- _ => rename H into MUb end. match goal with H : wmono ctasegs ma mb |- _ => rename H into WMb end.
      match goal with H : stk ctasegs mb _ _ |- _ => rename H into STb end. match goal with H : mem_inv ctasegs mb |- _ => rename H into MIb end.
      apply evt_done.
      assert (EPL : tlen_plen g op len = len - (go_p g - op)).
      { unfold CtColP.W_check_tlen_gen.tlen_plen. destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER in KI |- *; first [reflexivity| exfalso; apply KI; reflexivity]. }
      assert (MEMb : memA mb Σ4 st4 OW4 bo4 spent frame).
      { eapply (ctl_memA_munch ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc ma mb); [exact MEM| exact MUb| exact WMb| exact MIb| exact STb| | | | | | exact ESPA].
        - constructor; [| constructor]. right; right. exists (ql, f + 64, 8). cbn [blk_addr blk_size fst snd]. split; [exact HQL| clear; lia].
        - intros a HL. cbn [outside fst snd].
          pose proof (@lib_addr_apartA (push AR f 1) _ _ _ _ (ql, f + 64, 8) a HEAP4 ltac:(apply in_or_app; left; unfold actl_pbs; cbn; tauto)) as AP. cbn [blk_addr blk_size fst snd] in AP.
          destruct (Z_lt_le_dec a (f + 64)) as [L|L]; [clear - L; lia|]. destruct (Z_lt_le_dec a (f + 72)) as [L2|L2]; [| clear - L2; lia].
          exfalso. apply AP; [clear - L L2; lia| exact HL].
        - intros a [_ Hc]. cbn [outside fst snd]. destruct Hc as [H1|[H1|(b & Hb & Hr)]].
          + clear - H1 FLO SPAH. lia.
          + pose proof (client_static_lowA a H1) as Ha. unfold SEGTOP_A in Ha. clear - Ha G4. lia.
          + pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. clear - Hr O. lia.
        - intros a Ha. rewrite ctl_frameA_size in Ha. cbn [outside fst snd]. clear - Ha FLO. lia.
        - intros a [Ha _]. cbn [outside fst snd]. clear - Ha FLO SPAH. lia. }
      eapply FIN; [exact MEMb| | | | | ].
      + exact HPIC.
      + exact HPPC.
      + destruct TLCo as [a|]; [| exact I]. destruct HTLC as (vb & j & H). exists vb, j. destruct TB as (HBT & TB1 & TB2 & _).
        pose proof (OFFLB bt HBT) as O. unfold off_fr in O. change (fs_size 1) with 128 in O.
        eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MUb)| exact H| intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside fst snd]; clear - Hx O TB1 TB2; lia].
      + match goal with H : rw_cells ctasegs mb (f + 64) [C8 ?v] |- _ =>
          replace v with (Z_to_bv 64 (tlen_plen g op len)) in H; [exact H| rewrite EPL; rewrite ?(unsigned_lit (D + go_p g)) by (clear - D0 GB1 GB2 GB3 OP0 OPT D63 TL0; lia); first [reflexivity| f_equal; clear; lia| apply bv_eq; rewrite !Z_to_bv_unsigned; f_equal; lia] ] end.
      + exact OP.
  Qed.
End Act.

Section Act2.
  Hypothesis STRCPY : strcpy_icontract RT.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m3 : mem) (Σ Σ1 : rts RT) (OW LB K : list block) (E : ap_env) (lo : Z) (ras : list Z).
  Variables (D : Z) (d : list Z) (op len PIC PPC : Z) (TLCo ot : option Z) (f spa : Z) (gg : nat) (junk gj : list byte) (bd bt : block) (qp ql qt qc : bptr).
  Hypothesis FACTS : ctl_factsA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m3 Σ Σ1 OW LB K E lo ras D d op len PIC PPC TLCo ot f spa gg junk gj bd bt.
  Local Notation pbs := (actl_pbs f qp ql qt qc).
  Local Notation XX := (ctl_XX PIC PPC TLCo).
  Local Notation memA := (ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc).
  Local Notation g := (get_object d op len).
  Variables (j0 j8 j16 j24 j32 j40 j128 j136 : list byte).
  Local Notation frame := (ctl_frameA j0 j8 j16 j24 j32 j40 f PIC PPC len ot j128 j136 gg junk).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ctl_okA : forall {X} (KE KW KS : @AM bptr X) (Q : X * ap_st bptr -> rts RT -> machine_state -> Prop)
      (x1 x11 x12 x13 x14 x16 x20 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (ma : mem) (Σ4 : rts RT) (st4 : ap_st bptr) (OW4 : list block) (bo4 : Z * Z) (bi bc : bv 8) (jl : list byte),
    go_err g = None ->
    memA ma Σ4 st4 OW4 bo4 1 frame -> uw_chain USTACK_TOP ma spa (bv_unsigned sp) (bv_unsigned ra :: ras) ->
    rw_cells ctasegs ma PIC [C1 bi; C1 bc; CB 8 jl] -> rw_cells ctasegs ma PPC [C8 (Z_to_bv 64 (D + op))] -> ctl_tlcA TLCo ma ->
    rw_cells ctasegs ma (f + 32) [C4 (Z_to_bv 64 (go_tag g))] -> rw_cells ctasegs ma (f + 48) [C4 (Z_to_bv 64 (go_cls g))] ->
    rw_cells ctasegs ma (f + 64) [C8 (Z_to_bv 64 (go_len g))] -> rw_cells ctasegs ma (f + 96) [C8 (Z_to_bv 64 (D + go_p g))] ->
    (forall t st' Σ' ms' bi' bc' jl',
       ot = Some t -> go_err g = None -> (go_tag g <> t \/ go_cls g <> 0) ->
       ctl_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (ctl_costA g ot) PIC PPC TLCo 0 [C1 bi'; C1 bc'; CB 8 jl'] (D + op) st' Σ' ms' ->
       implAp (KW st') Σ' Q ms') ->
    (forall st' Σ' ms',
       go_err g = None -> match ot with Some t => go_tag g = t /\ go_cls g = 0 | None => True end ->
       ctl_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (ctl_costA g ot) PIC PPC TLCo 1
                 [C1 (Z_to_bv 8 (Z.land (go_ret g) 1)); C1 (Z_to_bv 8 (Z.land (go_ret g) 32)); C8 (wz (tlen_plen g op len))] (D + go_p g) st' Σ' ms' ->
       implAp (KS st') Σ' Q ms') ->
    implAp (tlen_tree g ot KE KW KS st4) Σ4 Q
           (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 (f + 48)) (Z_to_bv 64 0) (Z_to_bv 64 PPC) sp (Z_to_bv 64 spa)
                    (Z_to_bv 64 (go_ret g)) x11 x12 x13 x14 (Z_to_bv 64 (D + op)) x16 (Z_to_bv 64 0)
                    (Z_to_bv 64 f) (Z_to_bv 64 (ctl_tlc TLCo)) x20 (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) (Z_to_bv 64 (f + 64)) x25 x26 (Z_to_bv 64 SHB) x28 x29 x30 x31)
               F (Z_to_bv 64 0x242a94) fc None ma (seg_rom ctasegs)).
  Proof.
    intros until jl. intros EG MEM UW4 HPIC HPPC HTLC OT4 OC4 OL OP KW_ KS_. ctl_facts FACTS.
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7).
    pose proof MEM as (PRE4 & KEPT4 & AX4 & CRED4 & FRL & FRH). unfold ctl_frameA in FRL.
    pose proof PRE4 as (HEAP4 & _ & _ & _ & ST4 & _ & _ & _ & _ & MI4 & _ & _). rewrite ESPA in ST4.
    pose proof (go_ret_cases d op len) as RC. cbv zeta in RC.
    pose proof (go_cls_cases d op len) as CC. cbv zeta in CC.
    pose proof (go_tag_range d op len) as TG. cbv zeta in TG. unfold INT_MAX in TG.
    assert (RB : 0 <= go_ret g < 64) by (destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER; clear; lia).
    assert (FLO : f + 128 <= spa) by (clear - G3 CEIL LOSP SPAL; plia).
    (* [comment removed for export] *)
    assert (CSTW : forall t, ot = Some t -> (go_tag g <> t \/ go_cls g <> 0) -> ctl_costA g ot = 1 + GETOBJ_ERR_COST_A).
    { intros t -> NE. unfold ctl_costA. rewrite EG. destruct NE as [NE|NE]; [destruct (Z.eqb_spec (go_tag g) t); [exfalso; exact (NE ltac:(assumption))| reflexivity]|].
      destruct (Z.eqb_spec (go_cls g) 0); [exfalso; exact (NE ltac:(assumption))|]. rewrite orb_true_r. reflexivity. }
    assert (CSTS : match ot with Some t => go_tag g = t /\ go_cls g = 0 | None => True end -> ctl_costA g ot = 1).
    { intros HM. unfold ctl_costA. rewrite EG. destruct ot as [t|]; [| reflexivity]. destruct HM as [-> ->]. rewrite !Z.eqb_refl. reflexivity. }
    unfold CtColP.W_check_tlen_gen.tlen_tree. rewrite EG.
    pose proof (munch_refl (match TLCo with Some a => [(a, a + 1)] | None => [] end)%Z ma) as MU. pose proof (wmono_refl ctasegs ma) as WM.
    (* [comment removed for export] *)
    assert (WRONG : forall t (y11 y12 : word), ot = Some t -> (go_tag g <> t \/ go_cls g <> 0) ->
      evt ctasegs (fun ms' => implAp (abind (err_raise RS_tlen_wrong_tag) (fun _ : unit => KW) st4) Σ4 Q ms')
        (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 (f + 48)) (Z_to_bv 64 0) (Z_to_bv 64 PPC) sp (Z_to_bv 64 spa)
                 (Z_to_bv 64 (go_ret g)) y11 y12 (Z_to_bv 64 len) x14 (Z_to_bv 64 (D + op)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 0)
                 (Z_to_bv 64 f) (Z_to_bv 64 (ctl_tlc TLCo)) x20 (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) (Z_to_bv 64 (f + 64)) x25 x26 (Z_to_bv 64 SHB) x28 x29 x30 x31)
            F (Z_to_bv 64 0x242bfc) fc None ma (seg_rom ctasegs))).
    { intros t y11 y12 ET NE. clear MU WM. pose proof (munch_refl (@nil (Z * Z)) ma) as MU. pose proof (wmono_refl ctasegs ma) as WM.
      step. step. if_true. apply evt_done.
      eapply implAp_abind.
      { eapply (ctl_raiseA STRCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS
                  0x242cfc 1236 168 RS_tlen_wrong_tag 5%nat);
          [right; repeat split; reflexivity| exact MEM| rewrite KC3, KC6; clear; lia| exact UW4| rewrite ctl_frameA_size; clear - GSZ; lia
          | exact HPIC| reflexivity| exact HPPC| exact HTLC]. }
      intros r Σ7 ms7 RP. cbv beta.
      eapply (ctl_ret0A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS (KW (snd r)) Q r Σ7 ms7);
        [exact RP| reflexivity|].
      intros Σ' ms' PO. eapply (KW_ t); [exact ET| exact EG| exact NE| rewrite (CSTW t ET NE); exact PO]. }
    assert (BT : forall t, ot = Some t -> (go_tag g <> t \/ go_cls g <> 0) -> negb (go_tag g =? t) || negb (go_cls g =? 0) = true).
    { intros t _ NE. apply orb_true_iff. destruct NE as [NE'|NE']; [left| right]; apply negb_true_iff; apply Z.eqb_neq; exact NE'. }
    destruct ot as [t|]; cbn [ctl_xt] in *.
    - (* [comment removed for export] *)
      pose proof OT as TR.
      apply implAp_from_evt.
      (* [comment removed for export] *)
      step. step. if_cases KB; zc KB; [exfalso; apply KB; rewrite ?(unsigned_lit (go_ret g)) by (clear - RB; lia); destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER; reflexivity|]. clear KB.
      step. step. step.
      step. if_cases KX; zc KX; [exfalso; revert KX; rewrite ?signed_small by (clear - TR; lia); clear - TR; lia|]. clear KX.
      (* [comment removed for export] *)
      step. rewrite (sx32_small (go_tag g)) by (clear - TG; lia).
      step. if_cases KT; zc KT.
      + (* [comment removed for export] *)
        assert (NE : go_tag g <> t \/ go_cls g <> 0).
        { left. intros E0. apply KT. subst t. reflexivity. }
        eapply evt_mono; [eapply (WRONG t); [reflexivity| exact NE]|].
        intros ms' H. cbv beta in H. rewrite (BT t eq_refl NE). exact H.
      + assert (ETG : go_tag g = t) by (revert KT; rewrite ?unsigned_lit by (clear - TR TG; lia); clear; intros KT; lia).
        (* [comment removed for export] *)
        step. rewrite (sx32_small (go_cls g)) by (clear - CC; lia). step.
        step. if_cases KC; zc KC.
        * (* [comment removed for export] *)
          assert (NE : go_tag g <> t \/ go_cls g <> 0).
          { right. intros E0. apply KC. rewrite E0. reflexivity. }
          eapply evt_mono; [eapply (WRONG t); [reflexivity| exact NE]|].
          intros ms' H. cbv beta in H. rewrite (BT t eq_refl NE). exact H.
        * assert (ECL : go_cls g = 0) by (revert KC; rewrite ?unsigned_lit by (clear - CC; lia); clear; intros KC; lia).
          replace (negb (go_tag g =? t) || negb (go_cls g =? 0)) with false by (rewrite ETG, ECL, !Z.eqb_refl; reflexivity).
          (* [comment removed for export] *)
          destruct TLCo as [tlc|].
          -- destruct TB as (HBT & TB1 & TB2 & TB8). destruct HTLC as (vb & jt & HT). cbn [ctl_tlc] in *.
             assert (HBT' : In bt (OW4 ++ pbs ++ LB)) by (apply in_or_app; right; apply in_or_app; right; exact HBT).
             pose proof (@AH_range_gen (push AR f 1) _ _ _ _ bt HEAP4 HBT') as (BT0 & _ & _ & BT3 & BT4).
             change (@BnHeapA.ACEIL (push AR f 1)) with (@BnHeapA.ACEIL AR) in BT3.
             pose proof (proj2 (@AH_acc (push AR f 1) _ _ _ _ bt HEAP4 HBT')) as ACCT.
             pose proof (@AH_offsh (push AR f 1) _ _ _ _ bt HEAP4 HBT') as OFFT.
             assert (ETLC : bv_unsigned (Z_to_bv 64 tlc) = tlc) by (apply unsigned_lit; clear - BT0 BT3 TB1 TB2 CN; plia).
             assert (OFF : offshW [(tlc, tlc + 1)]%Z) by (cbn [offshW]; clear - OFFT TB1 TB2; unfold SHLO, SHHI in *; lia).
             pose proof (OFFLB bt HBT) as OBT. unfold off_fr in OBT. change (fs_size 1) with 128 in OBT.
             step. if_cases K9; zc K9; [exfalso; rewrite ?ETLC in K9; clear - K9 BT0 TB1; lia|]. clear K9.
             step.
             lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mb end.
             match goal with H : munch _ ma mb |- _ => rename H into MUb end. match goal with H : wmono ctasegs ma mb |- _ => rename H into WMb end.
             match goal with H : stk ctasegs mb _ _ |- _ => rename H into STb end. match goal with H : mem_inv ctasegs mb |- _ => rename H into MIb end.
             apply evt_done.
             assert (OUTb : forall a, (a < tlc \/ tlc + 1 <= a) -> outside [(tlc, tlc + 1)]%Z a) by (intros a Ha; cbn [outside fst snd]; clear - Ha; lia).
             assert (MEMb : ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC (Some tlc) f spa qp ql qt qc mb Σ4 st4 OW4 bo4 1 (ctl_frameA j0 j8 j16 j24 j32 j40 f PIC PPC len (Some t) j128 j136 gg junk)).
             { eapply (ctl_memA_munch ra sp s0 m Σ LB K E lo ras PIC PPC (Some tlc) f spa qp ql qt qc ma mb); [exact MEM| exact MUb| exact WMb| exact MIb| exact STb| | | | | | exact ESPA].
               - constructor; [| constructor]. right; right. exists bt. cbn [fst snd]. split; [exact HBT'| clear - TB1 TB2; lia].
               - intros a HL. pose proof (@lib_addr_apartA (push AR f 1) _ _ _ _ bt a HEAP4 ltac:(apply in_or_app; right; exact HBT)) as AP.
                 destruct (Z_lt_le_dec a tlc) as [L|L]; [apply OUTb; left; exact L|]. destruct (Z_lt_le_dec a (tlc + 1)) as [L2|L2]; [| apply OUTb; right; exact L2].
                 exfalso. apply AP; [clear - L L2 TB1 TB2; lia| exact HL].
               - intros a [HX _]. unfold ctl_XX, LIBW_A in HX. cbn [rin_ivs fst snd app] in HX. apply OUTb. clear - HX. lia.
               - intros a Ha. apply OUTb. clear - Ha BT3 TB2 CEIL LOSP SPAL. plia.
               - intros a [Ha _]. apply OUTb. clear - Ha BT3 TB2 CEIL LOSP SPAL. plia. }
             assert (OUTS : forall A cs, rw_cells ctasegs ma A cs -> (A + Z.of_nat (cells_size cs) <= tlc \/ tlc + 1 <= A) -> rw_cells ctasegs mb A cs).
             { intros A cs HC HA. eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MUb)| exact HC| intros a Ha; apply OUTb; clear - Ha HA; lia]. }
             eapply (ctl_finA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS j0 j8 j16 j24 j32 j40 j128 j136 (KS st4) Q); [exact EG| exact MEMb| | | | | | ].
             ++ first [exact HPIC| apply OUTS; [exact HPIC| cbn; clear - BT3 TB2 CEIL LOSP PIClo; plia]].
             ++ first [exact HPPC| apply OUTS; [exact HPPC| cbn; clear - BT3 TB2 CEIL LOSP PPClo; plia]].
             ++ cbn [ctl_tlcA]. match goal with H : rw_cells ctasegs mb tlc ?cs |- _ => eexists; exists jt; exact H end.
             ++ first [exact OL| apply OUTS; [exact OL| cbn; clear - OBT TB1 TB2; lia]].
             ++ first [exact OP| apply OUTS; [exact OP| cbn; clear - OBT TB1 TB2; lia]].
             ++ intros Σ' ms' PO. eapply KS_; [exact EG| split; [exact ETG| exact ECL]| rewrite (CSTS (conj ETG ECL)); exact PO].
          -- cbn [ctl_tlc] in *. step. if_true. apply evt_done.
             eapply (ctl_finA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS j0 j8 j16 j24 j32 j40 j128 j136 (KS st4) Q); [exact EG| exact MEM| exact HPIC| exact HPPC| exact I| exact OL| exact OP|].
             intros Σ' ms' PO. eapply KS_; [exact EG| split; [exact ETG| exact ECL]| rewrite (CSTS (conj ETG ECL)); exact PO].
    - (* [comment removed for export] *)
      apply implAp_from_evt.
      step. step. if_cases KB; zc KB; [exfalso; apply KB; rewrite ?(unsigned_lit (go_ret g)) by (clear - RB; lia); destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER; reflexivity|]. clear KB.
      step. step. step.
      step. if_true. apply evt_done.
      eapply (ctl_finA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS j0 j8 j16 j24 j32 j40 j128 j136 (KS st4) Q); [exact EG| exact MEM| exact HPIC| exact HPPC| exact HTLC| exact OL| exact OP|].
      intros Σ' ms' PO. eapply KS_; [exact EG| exact I| rewrite (CSTS I); exact PO].
  Qed.
End Act2.
End WithRT.
