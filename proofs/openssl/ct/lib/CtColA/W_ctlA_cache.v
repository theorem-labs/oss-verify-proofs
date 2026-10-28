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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA W_check_tlen_genA W_ctlA_defs W_ctlA_exit W_ctlA_raise W_ctlA_ok.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
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
  Variables (D : Z) (d : list Z) (op len PIC PPC : Z) (tlc : Z) (ot : option Z) (f spa : Z) (gg : nat) (junk gj : list byte) (bd bt : block) (qp ql qt qc : bptr).
  Hypothesis FACTS : ctl_factsA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m3 Σ Σ1 OW LB K E lo ras D d op len PIC PPC (Some tlc) ot f spa gg junk gj bd bt.
  Local Notation pbs := (actl_pbs f qp ql qt qc).
  Local Notation XX := (ctl_XX PIC PPC (Some tlc)).
  Local Notation memA := (ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC (Some tlc) f spa qp ql qt qc).
  Local Notation g := (get_object d op len).
  Variables (j0 j8 j16 j128 j136 : list byte).
  (* [comment removed for export] *)
  Local Notation frame0 := (ctl_frame0A j0 j8 j16 (C8 (Z_to_bv 64 (D + op))) (C8 (Z_to_bv 64 (f + 48))) (C8 (Z_to_bv 64 0)) f PIC PPC len ot j128 j136 gg junk).
  Local Notation frame := (ctl_frameA j0 j8 j16 (cbytes (C8 (Z_to_bv 64 (D + op)))) (cbytes (C8 (Z_to_bv 64 (f + 48)))) (cbytes (C8 (Z_to_bv 64 0))) f PIC PPC len ot j128 j136 gg junk).

  (* [comment removed for export] *)
  Local Definition at_tailA {A} (t : aprog bptr A) (Q : A -> rts RT -> machine_state -> Prop) (Σ4 : rts RT) (st4 : ap_st bptr) (OW4 : list block) (bo4 : Z * Z) (spent : Z)
      (x10 : word) (cpic : list cell) (cl ct cc : cell) (F : bvmap 5 word) (fc : bv 32) (x28 x29 x30 x31 : word) : Prop :=
    forall (ma : mem) (x11 x12 x13 x14 x16 : word),
      memA ma Σ4 st4 OW4 bo4 spent frame -> uw_chain USTACK_TOP ma spa (bv_unsigned sp) (bv_unsigned ra :: ras) ->
      rw_cells ctasegs ma PIC cpic -> rw_cells ctasegs ma PPC [C8 (Z_to_bv 64 (D + op))] -> ctl_tlcA (Some tlc) ma ->
      rw_cells ctasegs ma (f + 32) [ct] -> rw_cells ctasegs ma (f + 48) [cc] -> rw_cells ctasegs ma (f + 64) [cl] -> rw_cells ctasegs ma (f + 96) [C8 (Z_to_bv 64 (D + go_p g))] ->
      implAp t Σ4 Q (MS (mkR (Z_to_bv 64 0x2429a0) (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 (f + 48)) (Z_to_bv 64 0) (Z_to_bv 64 PPC) sp (Z_to_bv 64 spa)
                          x10 x11 x12 x13 x14 (Z_to_bv 64 (D + op)) x16 (Z_to_bv 64 0)
                          (Z_to_bv 64 f) (Z_to_bv 64 tlc) (Z_to_bv 64 0) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (tlc + 4)) (Z_to_bv 64 (Z.shiftr tlc 3 + SHB)) (Z_to_bv 64 SHB) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x242a94) fc None ma (seg_rom ctasegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ctl_cacheA : forall {A} (t : aprog bptr A) (Q : A -> rts RT -> machine_state -> Prop)
      (t0 t1 t2 x10 a1 a2 a3 a4 a5 a6 a7 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m4 : mem) (Σ4 : rts RT) (st4 : ap_st bptr) (OW4 : list block) (bo4 : Z * Z) (spent : Z) (cpic : list cell) (jl j2 j3 j31 : list byte),
    memA m4 Σ4 st4 OW4 bo4 spent frame0 -> uw_chain USTACK_TOP m4 spa (bv_unsigned sp) (bv_unsigned ra :: ras) ->
    rw_cells ctasegs m4 PIC cpic -> cells_size cpic = 10%nat -> rw_cells ctasegs m4 PPC [C8 (Z_to_bv 64 (D + op))] ->
    rw_cells ctasegs m4 tlc [C1 (Z_to_bv 8 0); CB 31 j31] ->
    rw_cells ctasegs m4 (f + 32) [CB 4 j2] -> rw_cells ctasegs m4 (f + 48) [CB 4 j3] -> rw_cells ctasegs m4 (f + 64) [CB 8 jl] -> rw_cells ctasegs m4 (f + 96) [C8 (Z_to_bv 64 (D + go_p g))] ->
    0 <= go_p g - op <= len ->
    (* [comment removed for export] *)
    (Z.land (bv_unsigned x10) 129 <> 0 \/ (Z.land (bv_unsigned x10) 129 = 0 /\ jl = le8 (Z_to_bv 64 (go_len g)) /\ 0 <= go_len g /\ go_p g - op + go_len g <= len)) ->
    at_tailA t Q Σ4 st4 OW4 bo4 spent x10 cpic (CB 8 jl) (CB 4 j2) (CB 4 j3) F fc x28 x29 x30 x31 ->
    implAp t Σ4 Q (MS (mkR (Z_to_bv 64 0x2429a0) (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 spa)
                        x10 a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 f) (Z_to_bv 64 tlc) (Z_to_bv 64 0) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f)
                        (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (tlc + 4)) (Z_to_bv 64 (Z.shiftr tlc 3 + SHB)) (Z_to_bv 64 SHB) x28 x29 x30 x31)
                   F (Z_to_bv 64 0x2429a0) fc None m4 (seg_rom ctasegs)).
  Proof.
    intros until j31. intros MEM UW4 HPIC SZP HPPC HTLC OT4 OC4 OL4 OP4 HL B81 TAILK. ctl_facts FACTS.
    pose proof MEM as (PRE4 & KEPT4 & AX4 & CRED4 & FRL & FRH). unfold ctl_frame0A in FRL.
    pose proof PRE4 as (HEAP4 & _ & _ & _ & ST4 & _ & _ & _ & _ & MI4 & _ & _). rewrite ESPA in ST4.
    destruct TB as (HBT & TB1 & TB2 & TB8).
    assert (HBT' : In bt (OW4 ++ pbs ++ LB)) by (apply in_or_app; right; apply in_or_app; right; exact HBT).
    pose proof (@AH_range_gen (push AR f 1) _ _ _ _ bt HEAP4 HBT') as (BT0 & _ & _ & BT3 & BT4).
    change (@BnHeapA.ACEIL (push AR f 1)) with (@BnHeapA.ACEIL AR) in BT3.
    pose proof (proj2 (@AH_acc (push AR f 1) _ _ _ _ bt HEAP4 HBT')) as ACCT.
    pose proof (@AH_offsh (push AR f 1) _ _ _ _ bt HEAP4 HBT') as OFFT.
    pose proof (OFFLB bt HBT) as OBT. unfold off_fr in OBT. change (fs_size 1) with 128 in OBT.
    assert (ETLC : bv_unsigned (Z_to_bv 64 tlc) = tlc) by (apply unsigned_lit; clear - BT0 BT3 TB1 TB2 CN; plia).
    assert (TLCLO : tlc + 32 <= spa) by (clear - BT3 TB2 CEIL LOSP SPAL; plia).
    assert (FLO : f + 128 <= spa) by (clear - G3 CEIL LOSP SPAL; plia).
    pose proof (munch_refl [(tlc, tlc + 32)]%Z m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
    assert (OFF : offshW [(tlc, tlc + 32)]%Z) by (cbn [offshW]; clear - OFFT TB1 TB2; unfold SHLO, SHHI in *; lia).
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. step. step. step.
    (* [comment removed for export] *)
    ab_shload 4. step. step. step. step. step. rstep. rewrite ?zxb_z8, ?sxb_z8. if_false. step.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. step. step. ab_shload 4. step. step. rstep. rewrite ?zxb_z8, ?sxb_z8. if_false. step.
    (* [comment removed for export] *)
    step. step. step. ab_shload 4. step. rstep. rewrite ?zxb_z8, ?sxb_z8. if_false.
    step. zstep. unfold MallocRep.wz. rewrite ?(unsigned_lit (D + op)) by (clear - D0 OP0 OPT D63 TL0; lia). rewrite ?(unsigned_lit (D + go_p g)) by (clear - D0 OP0 OPT D63 TL0 HL; lia).
    replace (bv_swrap 32 (D + go_p g - (D + op))) with (go_p g - op) by (rewrite bn_swrap32_small by (clear - HL OPT D26 OP0 TL0; lia); clear; lia).
    step.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    ab_shload 1. rstep. rewrite ?zxb_z8, ?sxb_z8. if_false.
    step. zstep. step. step.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LR : 0 <= Z.land (bv_unsigned x10) 129 < 2 ^ 64).
    { pose proof (bv_unsigned_in_range 64 x10) as XR. unfold bv_modulus in XR. cbn in XR.
      split; [apply Z.land_nonneg; right; clear; lia|]. eapply Z.le_lt_trans; [apply land_le_lA; clear - XR; lia| clear - XR; lia]. }
    assert (ATT : forall mz (y11 y12 y13 y14 y16 : word),
      munch [(tlc, tlc + 32)]%Z m4 mz -> wmono ctasegs m4 mz -> mem_inv ctasegs mz -> stk ctasegs mz lo spa ->
      rw_cells ctasegs mz PIC cpic -> rw_cells ctasegs mz PPC [C8 (Z_to_bv 64 (D + op))] ->
      (exists cs, rw_cells ctasegs mz tlc cs /\ cells_size cs = 32%nat) ->
      rw_cells ctasegs mz (f + 32) [CB 4 j2] -> rw_cells ctasegs mz (f + 48) [CB 4 j3] -> rw_cells ctasegs mz (f + 64) [CB 8 jl] -> rw_cells ctasegs mz (f + 96) [C8 (Z_to_bv 64 (D + go_p g))] ->
      evt ctasegs (fun ms' => implAp t Σ4 Q ms')
        (MS (mkR (Z_to_bv 64 0x2429a0) (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 (f + 48)) (Z_to_bv 64 0) (Z_to_bv 64 PPC) sp (Z_to_bv 64 spa)
                 x10 y11 y12 y13 y14 (Z_to_bv 64 (D + op)) y16 (Z_to_bv 64 0)
                 (Z_to_bv 64 f) (Z_to_bv 64 tlc) (Z_to_bv 64 0) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 f) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (tlc + 4)) (Z_to_bv 64 (Z.shiftr tlc 3 + SHB)) (Z_to_bv 64 SHB) x28 x29 x30 x31)
            F (Z_to_bv 64 0x242a94) fc None mz (seg_rom ctasegs))).
    { intros mz y11 y12 y13 y14 y16 MUz WMz MIz STz HPICz HPPCz (cs & HTz & SZz) OTz OCz OLz OPz. apply evt_done.
      assert (OUTz : forall a, (a < tlc \/ tlc + 32 <= a) -> outside [(tlc, tlc + 32)]%Z a) by (intros a Ha; cbn [outside fst snd]; clear - Ha; lia).
      assert (MEMz : memA mz Σ4 st4 OW4 bo4 spent frame).
      { eapply ctl_memA_reframe; [| intros HF; apply (ctl_frame0A_cb mz spa); [reflexivity| reflexivity| reflexivity| exact HF]].
        eapply (ctl_memA_munch ra sp s0 m Σ LB K E lo ras PIC PPC (Some tlc) f spa qp ql qt qc m4 mz); [exact MEM| exact MUz| exact WMz| exact MIz| exact STz| | | | | | exact ESPA].
        - constructor; [| constructor]. right; right. exists bt. cbn [fst snd]. split; [exact HBT'| clear - TB1 TB2; lia].
        - intros a HLa. pose proof (@lib_addr_apartA (push AR f 1) _ _ _ _ bt a HEAP4 ltac:(apply in_or_app; right; exact HBT)) as AP.
          destruct (Z_lt_le_dec a tlc) as [L|L]; [apply OUTz; left; exact L|]. destruct (Z_lt_le_dec a (tlc + 32)) as [L2|L2]; [| apply OUTz; right; exact L2].
          exfalso. apply AP; [clear - L L2 TB1 TB2; lia| exact HLa].
        - intros a [HX _]. unfold ctl_XX, LIBW_A in HX. cbn [rin_ivs fst snd app] in HX. apply OUTz. clear - HX. lia.
        - intros a Ha. unfold ctl_frame0A in Ha. cbn [cells_size csize Nat.add] in Ha. apply OUTz. clear - Ha TLCLO. lia.
        - intros a [Ha _]. apply OUTz. clear - Ha TLCLO SPAH. lia. }
      assert (HTLCz : ctl_tlcA (Some tlc) mz).
      { apply rw_cells_CB_ofA in HTz. rewrite SZz in HTz. apply (cb_split_a mz tlc 1 31) in HTz.
        cut_hd HTz HV (tlc + 1). destruct (cb_byte_a _ _ _ HV) as [vb HV1]. join2 HV1 HTz. cbn [ctl_tlcA]. exists vb. eexists. exact HV1. }
      eapply (TAILK mz); [exact MEMz| | exact HPICz| exact HPPCz| exact HTLCz| exact OTz| exact OCz| exact OLz| exact OPz].
      eapply uw_chain_munchP; [exact MUz| exact UW4| intros a _ [Ha _]; apply OUTz; clear - Ha TLCLO SPAH; lia]. }
    (* [comment removed for export] *)
    destruct B81 as [B81|(B80 & Ejl & GL0 & GB3)].
    - step. if_cases KB; zc KB; [| exfalso; apply B81; revert KB; rewrite ?unsigned_lit by exact LR; clear; intros KB; lia].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mz end.
      eapply ATT; try eassumption. match goal with H : rw_cells ctasegs mz tlc ?cs |- _ => exists cs; split; [exact H| reflexivity] end.
    - subst jl. rewrite ?load_u64. match goal with H : rw_cells ctasegs _ tlc _ |- _ => rewrite ?load_u64 in H end.
      step. if_cases KB; zc KB; [exfalso; apply KB; rewrite ?unsigned_lit by exact LR; exact B80|].
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. step. if_cases KTL; zc KTL; [| exfalso; revert KTL; rewrite ?unsigned_lit by (clear - HL GL0 GB3 OPT D26 OP0 TL0; lia); rewrite ?signed_small by (clear - HL GL0 GB3 OPT D26 OP0 TL0; lia); clear - GB3; lia].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mz end.
      eapply ATT; try eassumption. match goal with H : rw_cells ctasegs mz tlc ?cs |- _ => exists cs; split; [exact H| reflexivity] end.
  Qed.
End Act.
End WithRT.
