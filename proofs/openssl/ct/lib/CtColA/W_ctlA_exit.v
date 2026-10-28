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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA W_check_tlen_genA W_ctlA_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Act.
  (* [comment removed for export] *)
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m3 : mem) (Σ Σ1 : rts RT) (OW LB K : list block) (E : ap_env) (lo : Z) (ras : list Z).
  Variables (D : Z) (d : list Z) (op len PIC PPC : Z) (TLCo ot : option Z) (f spa : Z) (gg : nat) (junk gj : list byte) (bd bt : block) (qp ql qt qc : bptr).
  Hypothesis FACTS : ctl_factsA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m3 Σ Σ1 OW LB K E lo ras D d op len PIC PPC TLCo ot f spa gg junk gj bd bt.
  Local Notation pbs := (actl_pbs f qp ql qt qc).
  Local Notation XX := (ctl_XX PIC PPC TLCo).
  Local Notation memA := (ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ctl_exitA : forall {A} (t : aprog bptr A) (Q : A -> rts RT -> machine_state -> Prop)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (mk : mem) (Σk : rts RT) (stk : ap_st bptr) (OWk : list block) (bok : Z * Z) (spent rv : Z) (cpic : list cell) (pp : Z)
      (j0 j8 j16 j24 j32 j40 : list byte) (j128 j136 : list byte),
    memA mk Σk stk OWk bok spent (ctl_frameA j0 j8 j16 j24 j32 j40 f PIC PPC len ot j128 j136 gg junk) ->
    rw_cells ctasegs mk PIC cpic -> cells_size cpic = 10%nat -> rw_cells ctasegs mk PPC [C8 (Z_to_bv 64 pp)] -> ctl_tlcA TLCo mk ->
    (forall Σ' ms', ctl_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K spent PIC PPC TLCo rv cpic pp stk Σ' ms' -> implAp t Σ' Q ms') ->
    implAp t Σk Q (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 f) x19 x20 (Z_to_bv 64 (shad f)) x22 (Z_to_bv 64 f) x24 x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 ACTL_EXIT) fc None mk (seg_rom ctasegs)).
  Proof.
    intros until j136. intros MEM HPIC SZP HPPC HTLC HK. ctl_facts FACTS.
    destruct MEM as (PRE4 & KEPT4 & AX4 & CRED4 & FRL & FRH).
    pose proof PRE4 as (HEAPk0 & ASk & IDSk & DCk & STk & _ & _ & _ & _ & MIk & _ & _). rewrite ESPA in STk.
    (* [comment removed for export] *)
    assert (HEAPk : @BnHeapA.AHEAP (push AR f 1) Σk OWk LB mk).
    { unfold actl_pbs in HEAPk0. cbn [app] in HEAPk0.
      do 4 (eapply (@frame_obj_close (push AR f 1)) in HEAPk0; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia]).
      exact HEAPk0. }
    clear HEAPk0.
    apply (rw_cells_cb_first mk spa _ 18) in FRL. cbn [cb_first csize cbytes ctl_frameA] in FRL.
    intros X2 Φ2 D2 SAFE2 LINK2. change (Z_to_bv 64 ACTL_EXIT) with (wz ACTL_EXIT). change (Z_to_bv 64 TP_A) with (wz TP_A).
    eapply (actl_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAPk | exact OFFLB | exact STk | exact CEIL | clear - LOSP SPAL; lia
      | exact TOP | clear - SPAL; lia | clear - SPAH; lia | exact GSZ | exact SAVJ | exact MIk | exact FRL | exact FRH | reflexivity |].
    intros Σ' m' x11' HEAP' CR' EL' ST' MI' AG'.
    eapply (implAp_elim t); [| exact SAFE2 | exact LINK2 | exact EL'].
    apply HK.
    (* [comment removed for export] *)
    assert (AGL : agree_on (lib_addr OWk) mk m').
    { eapply agree_on_mono; [exact AG'|]. intros a Ha. exact (lib_addr_aclient OWk LB spa a Ha). }
    assert (CST : forall A0 cs, rw_cells ctasegs mk A0 cs -> bv_unsigned sp <= A0 -> A0 + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs m' A0 cs).
    { intros A0 cs HC H1 H2. eapply rw_cells_agree; [exact AG'| exact HC|]. intros a Ha. left. clear - Ha H1 H2 SPAH. lia. }
    apply CST in HPIC; [| exact PIClo| rewrite SZP; clear - PIChi; lia]. apply CST in HPPC; [| exact PPClo| cbn; clear - PPChi; lia].
    assert (HTLC' : ctl_tlcA TLCo m').
    { destruct TLCo as [a|]; [| exact I]. destruct TB as (HBT & TB1 & TB2 & _). destruct HTLC as (vb & j & H). exists vb, j.
      eapply rw_cells_agree; [exact AG'| exact H|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; right. exists bt.
      split; [apply in_or_app; right; exact HBT| clear - Hx TB1 TB2; lia]. }
    unfold ctl_postA.
    exists x5, x6, x7, x11', x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F, fc, m', OWk, bok.
    split; [reflexivity|].
    split.
    { (* [comment removed for export] *)
      pose proof ASk as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & ODk)).
      unfold ap_preA. split; [exact HEAP'|]. split; [exact (ap_state_agree _ _ _ _ _ _ ASk AGL)|]. split; [exact IDSk|].
      split; [exact (data_cells_agree _ _ _ _ DCk AGL ODk)|]. split; [exact ST'|]. split; [exact CEIL|]. split; [clear - LOSP; lia|].
      split; [exact TOP|]. split; [exact AL16|]. split; [exact MI'|].
      split; [pose proof (af_credit_nonneg RT AF Σ' m' (AH_art _ _ _ _ HEAP')) as CNN; clear - CNN; lia|].
      clear - FRMX. lia. }
    split.
    { (* [comment removed for export] *)
      unfold ax_pres. eapply agree_on_trans; [exact AX4|]. eapply agree_on_mono; [exact AG'|].
      intros a [_ Hc]. destruct Hc as [H1|[H1|(b & Hb & Hr)]]; [left; clear - H1 SPAH; lia| right; left; exact H1| right; right].
      exists b. split; [apply in_or_app; right; exact Hb| exact Hr]. }
    split; [cbn [ar_RT push amb] in CRED4, CR'; clear - CRED4 CR'; lia|].
    split; [eapply (blocks_kept_post K stk OWk LB spa); [exact KEPT4| exact AG']|].
    split; [exact HPIC|]. split; [exact HPPC| exact HTLC'].
  Qed.
End Act.

(* [comment removed for export] *)
Section Act2.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m3 : mem) (Σ Σ1 : rts RT) (OW LB K : list block) (E : ap_env) (lo : Z) (ras : list Z).
  Variables (D : Z) (d : list Z) (op len PIC PPC : Z) (TLCo ot : option Z) (f spa : Z) (gg : nat) (junk gj : list byte) (bd bt : block) (qp ql qt qc : bptr).
  Hypothesis FACTS : ctl_factsA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m3 Σ Σ1 OW LB K E lo ras D d op len PIC PPC TLCo ot f spa gg junk gj bd bt.
  Local Notation pbs := (actl_pbs f qp ql qt qc).
  Local Notation XX := (ctl_XX PIC PPC TLCo).
  Local Notation memA := (ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ctl_ret0A : forall {A} (t : aprog bptr A) (Q : A -> rts RT -> machine_state -> Prop)
      (r : unit * ap_st bptr) (Σ7 : rts RT) (ms7 : machine_state) (spent : Z) (x20 x24 x25 x26 : word) (cpic : list cell) (pp : Z)
      (j0 j8 j16 j24 j32 j40 : list byte) (j128 j136 : list byte),
    ctl_rpostA ra sp gp s0 m Σ LB K E lo ras PIC PPC TLCo f spa qp ql qt qc spent (ctl_frameA j0 j8 j16 j24 j32 j40 f PIC PPC len ot j128 j136 gg junk) x20 x24 x25 x26 cpic pp r Σ7 ms7 ->
    cells_size cpic = 10%nat ->
    (forall Σ' ms', ctl_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K spent PIC PPC TLCo 0 cpic pp (snd r) Σ' ms' -> implAp t Σ' Q ms') ->
    implAp t Σ7 Q ms7.
  Proof.
    intros until j136. intros RP SZP HK. ctl_facts FACTS.
    destruct RP as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F7 & fc7 & m7 & OW7 & bo7 & -> & MEM7 & HPIC7 & HPPC7 & HTLC7).
    pose proof MEM7 as (PRE7 & KEPT7 & AX7 & CRED7 & FRL & FRH).
    pose proof PRE7 as (HEAP7 & _ & _ & _ & ST7 & _ & _ & _ & _ & MI7 & _ & _). rewrite ESPA in ST7.
    apply implAp_from_evt. unfold MallocRep.wz.
    destruct TLCo as [tlc|].
    - (* [comment removed for export] *)
      destruct TB as (HBT & TB1 & TB2 & TB8). destruct HTLC7 as (vb & jt & HTLC). cbn [ctl_tlc] in *.
      assert (HBT' : In bt (OW7 ++ pbs ++ LB)) by (apply in_or_app; right; apply in_or_app; right; exact HBT).
      pose proof (@AH_range_gen (push AR f 1) _ _ _ _ bt HEAP7 HBT') as (BT0 & _ & _ & BT3 & BT4).
      change (@BnHeapA.ACEIL (push AR f 1)) with (@BnHeapA.ACEIL AR) in BT3.
      pose proof (proj2 (@AH_acc (push AR f 1) _ _ _ _ bt HEAP7 HBT')) as ACCT.
      pose proof (@AH_offsh (push AR f 1) _ _ _ _ bt HEAP7 HBT') as OFFT.
      assert (ETLC : bv_unsigned (Z_to_bv 64 tlc) = tlc) by (apply unsigned_lit; clear - BT0 BT3 TB1 TB2 CN; plia).
      pose proof (munch_refl [(tlc, tlc + 1)]%Z m7) as MU. pose proof (wmono_refl ctasegs m7) as WM.
      assert (OFF : offshW [(tlc, tlc + 1)]%Z) by (cbn [offshW]; clear - OFFT TB1 TB2; unfold SHLO, SHHI in *; lia).
      step. if_cases KC; zc KC; [exfalso; rewrite ?ETLC in KC; clear - KC BT0 TB1; lia|]. clear KC.
      (* [comment removed for export] *)
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
      match goal with H : munch _ m7 m8 |- _ => rename H into MU8 end. match goal with H : wmono ctasegs m7 m8 |- _ => rename H into WM8 end.
      match goal with H : stk ctasegs m8 _ _ |- _ => rename H into ST8 end. match goal with H : mem_inv ctasegs m8 |- _ => rename H into MI8 end.
      apply evt_done.
      assert (MEM8 : ctl_memA ra sp s0 m Σ LB K E lo ras PIC PPC (Some tlc) f spa qp ql qt qc m8 Σ7 (snd r) OW7 bo7 spent (ctl_frameA j0 j8 j16 j24 j32 j40 f PIC PPC len ot j128 j136 gg junk)).
      { eapply (ctl_memA_munch ra sp s0 m Σ LB K E lo ras PIC PPC (Some tlc) f spa qp ql qt qc m7 m8); [exact MEM7| exact MU8| exact WM8| exact MI8| exact ST8| | | | | | exact ESPA].
        - constructor; [| constructor]. right; right. exists bt. cbn [fst snd]. split; [exact HBT'| clear - TB1 TB2; lia].
        - intros a HL. cbn [outside fst snd]. pose proof (@lib_addr_apartA (push AR f 1) _ _ _ _ bt a HEAP7 ltac:(apply in_or_app; right; exact HBT)) as AP.
          destruct (Z_lt_le_dec a tlc) as [L|L]; [clear - L; lia|]. destruct (Z_lt_le_dec a (tlc + 1)) as [L2|L2]; [| clear - L2; lia].
          exfalso. apply AP; [clear - L L2 TB1 TB2; lia| exact HL].
        - intros a [HX _]. unfold ctl_XX, LIBW_A in HX. cbn [rin_ivs fst snd app] in HX. cbn [outside fst snd]. clear - HX. lia.
        - intros a Ha. cbn [outside fst snd]. clear - Ha BT3 TB2 CEIL LOSP SPAL. plia.
        - intros a [Ha _]. cbn [outside fst snd]. clear - Ha BT3 TB2 CEIL LOSP SPAL. plia. }
      eapply (ctl_exitA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS t Q); [exact MEM8| | exact SZP| | | exact HK].
      + exact HPIC7.
      + exact HPPC7.
      + cbn [ctl_tlcA]. match goal with H : rw_cells ctasegs m8 tlc ?cs |- _ => eexists; exists jt; exact H end.
    - (* [comment removed for export] *)
      cbn [ctl_tlc] in *.
      pose proof (munch_refl (@nil (Z * Z)) m7) as MU. pose proof (wmono_refl ctasegs m7) as WM.
      step. if_true. step. step. apply evt_done.
      eapply (ctl_exitA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FACTS t Q); [exact MEM7| exact HPIC7| exact SZP| exact HPPC7| exact I| exact HK].
  Qed.
End Act2.
End WithRT.
