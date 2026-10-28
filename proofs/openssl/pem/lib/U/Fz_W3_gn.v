(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_tail Fz_W3_dec
     Fz_W3_endl Fz_W3_gnlem F_strncmp.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

Ltac hd_core_by ER BLEN SA SB SBIG MAXT MAXO DNT DNO GOT ROLE OWNN NN LBN NMC NONUL OWNL LBS LBC MBT MBO ELB CFRESH EL NDT OUT :=
  unfold hd_core; cbv zeta;
  split; [exact ER|]; split; [exact BLEN|]; split; [exact SA|]; split; [exact SB|]; split; [exact SBIG|];
  split; [exact MAXT|]; split; [exact MAXO|]; split; [exact DNT|]; split; [exact DNO|]; split; [exact GOT|]; split; [exact ROLE|];
  split; [exact OWNN|]; split; [exact NN|]; split; [exact LBN|]; split; [exact NMC|]; split; [exact NONUL|]; split; [exact OWNL|]; split; [exact LBS|];
  split; [exact LBC|]; split; [exact MBT|]; split; [exact MBO|]; split; [exact ELB|]; split; [exact CFRESH|]; split; [exact EL|];
  split; [exact NDT| exact OUT].
Ltac hd_inv_by ER REM BLEN SA SB SBIG LSUM MAXT MAXO DNT DNO GOT ROLE LEN OWNN NN LBN NMC NONUL OWNL LBS LBC NULk MBT MBO ELB CFRESH EL NDT OUT :=
  unfold hd_inv; split; [hd_core_by ER BLEN SA SB SBIG MAXT MAXO DNT DNO GOT ROLE OWNN NN LBN NMC NONUL OWNL LBS LBC MBT MBO ELB CFRESH EL NDT OUT|];
  split; [exact REM|]; split; [exact LSUM|]; split; [exact LEN| exact NULk].

Section W3. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
  Local Notation er0_callI := (er0_call errst_at_rest errst_fp errst_rest_agree errst_fp_where).
  Local Notation libenv_cfrI := (libenv_cfr libenv libenv_fp libenv_agree libenv_fp_where).

  Local Notation com_segI := (com_seg libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation er0_segI := (er0_seg errst_at_rest errst_fp errst_rest_agree errst_fp_where).

  Lemma t_signed_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
  Proof. intros z Hz. rewrite zb_signed. rewrite unsigned_lit by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia. Qed.

  Theorem GN1_proof : forall N,
    sanitize_line_stmt -> NAME_stmt libenv errst_at_rest errst_live -> GNG_at libenv errst_at_rest errst_live N -> GN_at libenv errst_at_rest errst_live N.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros N SAN NAMEP GNGP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 a0 a2 a4 a5 a6 a7 s2 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l11 ta tb
           ql LB1 hBv dBv len fc fl bs KX KY methX methY.
    cbv zeta. intros MEAS COM ER0 REM BOFF BLEN RA6 RB5 RBIG6 LOC OWNL LBS LBC LEN NULk FC FL MBT KXN MBO KYN ELB CFRESH EL NDT OUT.
    unfold sanitize_line_stmt in SAN. unfold NAME_stmt, J_NAME in NAMEP. unfold GNG_at, J_GNG in GNGP.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_GN, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (RL1 & _ & _ & RL2 & _).
    unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RL2.
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    assert (HWs : Forall (wfree LBc (e_lo en) (bv_unsigned (e_sp en) + 32) (fun q : bptr => q <> ql))
                    [(bv_unsigned (e_sp en) + -208 + -112, bv_unsigned (e_sp en) + -208); (LB1, LB1 + 256)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia|]. apply Forall_cons; [| apply Forall_nil].
      right. exists (ql, LB1, 256). split; [exact (proj1 OWNL)|]. split; [intros X; apply X; reflexivity|]. unfold blk_addr, blk_size; cbn [fst snd]. clear; lia. }
    assert (HXT : forall q, mbio_T KX q -> q <> ql) by (intros q Hq E; subst q; apply (DJX ql); [apply mbio_T_blocks; exact Hq| apply in_or_app; right; left; reflexivity]).
    assert (HXO : forall q, mbio_T KY q -> q <> ql) by (intros q Hq E; subst q; apply (DJY ql); [apply mbio_T_blocks; exact Hq| left; reflexivity]).
    assert (HXE : e_pe en <> ql) by (intros E; apply (DJC ql); [do 2 (apply in_or_app; right); left; reflexivity| left; exact E]).
    assert (HXB : forall b, In b (e_LBall en) -> blk_id b <> ql) by (intros b Hb E; apply (CFRESH _ Hb); rewrite E; do 2 (apply in_or_app; right); left; reflexivity).
    hide ELB. hide ROOM. hide CG.
    pose proof (munch_refl [(bv_unsigned (e_sp en) + -208 + -112, bv_unsigned (e_sp en) + -208); (LB1, LB1 + 256)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut;
      [ eapply (SAN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LB1 len fl fc (e_lo en) bs);
        [ reflexivity| reflexivity| reflexivity| reflexivity| exact RL1| exact RL2| exact LEN| exact FL| exact FC| exact LBS| exact LBC| exact NULk
        | rewrite unsigned_lit by (clear - SPR SLO LO GLO; lia); exact ST| exact LO| rewrite unsigned_lit by (clear - SPR SLO LO GLO; lia); unfold SAN_STACK; clear - SLO; lia| exact MI ]
      | ]
    end.
    cbv beta. intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & len' & bs' & m1 & -> & LEN' & MU1 & WM1 & MI1 & ST1 & LBS1 & LBC1 & NL1 & NUL1).
    rewrite !unsigned_lit in MU1 by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in ST1 by (clear - SPR SLO LO GLO; lia). th_ret_lit.
    replace (bv_unsigned (e_sp en) + -208 - 112) with (bv_unsigned (e_sp en) + -208 + -112) in MU1 by (clear; lia).
    clear LBC. transport_after_call usegs m m1 MU1 WM1. clear MU1 WM1 MI. try clear ST.
    Ltac sync_at mX ql F1 F2 F3 F4 :=
      lazymatch goal with | COM : pem_com _ ?en ?s ?LBc ?Lc ?f ?m0 ?off ?rem ?rA ?rB ?rBig |- _ =>
      lazymatch goal with | MU : munch ?W m0 mX |- _ =>
      lazymatch goal with | WM : wmono usegs m0 mX |- _ =>
      lazymatch goal with | MIx : mem_inv usegs mX |- _ =>
      lazymatch goal with | STx : stk usegs mX _ _ |- _ =>
      lazymatch goal with | CST : cstate s LBc _ Lc m0 _ _ _ _ |- _ =>
      lazymatch goal with | ER0 : _ (e_E en) [] m0 |- _ =>
      lazymatch goal with | INE : In (e_pe en, e_E en, 904) LBc |- _ =>
      lazymatch goal with | HWs : Forall _ W |- _ =>
      lazymatch goal with | MBT : mbio_rep m0 LBc Lc ?KT ?tmpv ?methT ?lenT ?maxT 0, MBO : mbio_rep m0 LBc Lc ?KO ?ov ?methO ?lenO ?maxO 0,
                            HXT : (forall q, mbio_T ?KT q -> q <> ql), HXO : (forall q, mbio_T ?KO q -> q <> ql) |- _ =>
      lazymatch goal with | HXE : e_pe en <> ql |- _ =>
      lazymatch goal with | HXB : (forall b, In b (e_LBall en) -> blk_id b <> ql) |- _ =>
        let COMx := fresh "COM2" in let ERx := fresh "ER2" in let MBTx := fresh "MBT2" in let MBOx := fresh "MBO2" in
        assert (COMx : pem_com libenv en s LBc Lc f mX off rem rA rB rBig)
          by (eapply (com_segI en s LBc Lc f m0 off rem rA rB rBig W mX (fun q => q <> ql));
              [exact COM| exact MU| exact WM| exact MIx| exact STx| exact HWs| exact HXB| unfold e_PL; cbn [disjoint_from fst snd]; clear - F1 F2 F3 F4; lia]);
        assert (ERx : errst_at_rest (e_E en) [] mX)
          by (eapply (er0_segI W en m0 mX) with (EX := fun q => q <> ql) (hi := bv_unsigned (e_sp en) + 32); [exact ER0| exact MU| exact WM| exact CST| exact INE| exact HWs| exact HXE]);
        assert (MBTx : mbio_rep mX LBc Lc KT tmpv methT lenT maxT 0)
          by (eapply (mb_seg W m0 mX) with (EX := fun q => q <> ql) (hi := bv_unsigned (e_sp en) + 32); [exact MBT| exact CST| exact MU| exact WM| exact HWs| exact HXT]);
        assert (MBOx : mbio_rep mX LBc Lc KO ov methO lenO maxO 0)
          by (eapply (mb_seg W m0 mX) with (EX := fun q => q <> ql) (hi := bv_unsigned (e_sp en) + 32); [exact MBO| exact CST| exact MU| exact WM| exact HWs| exact HXO])
      end end end end end end end end end end end end.
    (* [comment removed for export] *)
    lazymatch goal with H : mem_inv usegs m1 |- _ => rename H into MI1' end.
    assert (BGB : bytes_at usegs m1 0x20527 pem_begin_str) by (apply ro_bytes_at; [exact MI1'| clear; lia| rewrite pem_begin_len; clear; lia| exact pem_begin_ro]).
    pose proof (rw_cells_bytes_at _ _ _ _ LBC1) as LBB1. cbn [cells_bytes cbytes] in LBB1. rewrite app_nil_r in LBB1.
    destruct (strncmp_model_total bs' pem_begin_str 11) as (v1 & V1); [clear; lia| rewrite LBS1; clear; lia| rewrite pem_begin_len; clear; lia|].
    ths. ths. ths. ths. ths.
    tcall (strncmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs' pem_begin_str v1).
    all: try first [eassumption | clear - RL1 RL2 LO SLO SPR; lia].
    cbv beta delta [mkR].
    ths. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => sync_at mx ql RL2 LO SLO SPR end. chere. unfold hideP in ELB.
      lazymatch goal with COM2 : pem_com _ en s LBc Lc f ?mx off rem rA rB rBig, ER2 : _ (e_E en) [] ?mx, MBT2 : mbio_rep ?mx LBc Lc KX _ _ _ _ _, MBO2 : mbio_rep ?mx LBc Lc KY _ _ _ _ _,
                           LOCx : rw_cells usegs ?mx (bv_unsigned (e_sp en) + -208) _, OUTx : rw_cells usegs ?mx (bv_unsigned (e_sp en)) _, LBCx : rw_cells usegs ?mx LB1 _ |- _ =>
      eapply (GNGP en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 l4 l5 l11 ta tb ql LB1 hBv dBv fl bs' KX KY methX methY);
        [exact MEAS| exact COM2| exact ER2| exact REM| exact BOFF| exact BLEN| exact RA6| exact RB5| exact RBIG6| unfold pem_loc; exact LOCx| exact OWNL| exact LBS1| exact LBCx
        | exact FL| exact MBT2| exact KXN| exact MBO2| exact KYN| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUTx] end.
    - (* [comment removed for export] *)
      assert (V10 : v1 = 0) by (eapply strncmp_reg_zero; [exact V1| exact K1]).
      ths. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => sync_at mx ql RL2 LO SLO SPR end. chere. unfold hideP in ELB.
        lazymatch goal with COM2 : pem_com _ en s LBc Lc f ?mx off rem rA rB rBig, ER2 : _ (e_E en) [] ?mx, MBT2 : mbio_rep ?mx LBc Lc KX _ _ _ _ _, MBO2 : mbio_rep ?mx LBc Lc KY _ _ _ _ _,
                             LOCx : rw_cells usegs ?mx (bv_unsigned (e_sp en) + -208) _, OUTx : rw_cells usegs ?mx (bv_unsigned (e_sp en)) _, LBCx : rw_cells usegs ?mx LB1 _ |- _ =>
        eapply (GNGP en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 l4 l5 l11 ta tb ql LB1 hBv dBv fl bs' KX KY methX methY);
          [exact MEAS| exact COM2| exact ER2| exact REM| exact BOFF| exact BLEN| exact RA6| exact RB5| exact RBIG6| unfold pem_loc; exact LOCx| exact OWNL| exact LBS1| exact LBCx
          | exact FL| exact MBT2| exact KXN| exact MBO2| exact KYN| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUTx] end.
      + (* [comment removed for export] *)
        assert (L6 : 6 <= len') by (rewrite ?t_signed_small in K2 by (clear - LEN LEN'; lia); rewrite ?unsigned_lit in K2 by (clear - LEN LEN'; lia); clear - K2 LEN LEN'; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
        lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
        lazymatch goal with H : bytes_at usegs m2 LB1 bs' |- _ => rename H into LBB2 end.
        assert (TLB : bytes_at usegs m2 0x341ae pem_tail6_str) by (apply ro_bytes_at; [exact MI2| clear; lia| rewrite pem_tail6_len; clear; lia| exact pem_tail6_ro]).
        assert (SFX : bytes_at usegs m2 (LB1 + len' + -6) (skipn (Z.to_nat (len' - 6)) bs')).
        { pose proof LBB2 as X. rewrite <- (firstn_skipn (Z.to_nat (len' - 6)) bs') in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X. destruct X as [_ X].
          rewrite firstn_length_le in X by (rewrite LBS1; clear - LEN LEN'; lia). replace (LB1 + Z.of_nat (Z.to_nat (len' - 6))) with (LB1 + len' + -6) in X by (clear - L6; lia). exact X. }
        destruct (strncmp_model_total (skipn (Z.to_nat (len' - 6)) bs') pem_tail6_str 6) as (v2 & V2); [clear; lia| rewrite skipn_length, LBS1; clear - LEN LEN' L6; lia| rewrite pem_tail6_len; clear; lia|].
        ths. if_cases KC1; zify_cond KC1. { exfalso. pose proof alloc_ceiling_lt_2p47 as ACL. clear - KC1 RL2 LEN LEN' ACL; lia. } clear KC1.
        ths. ths. if_cases KC2; zify_cond KC2. { exfalso. clear - KC2 RL1 L6; lia. } clear KC2.
        ths. ths. ths. ths.
        tcall (strncmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (skipn (Z.to_nat (len' - 6)) bs') pem_tail6_str v2).
        all: try first [eassumption | clear - RL1 RL2 LO SLO SPR LEN LEN' L6; lia].
        cbv beta delta [mkR].
        ths. if_cases K3; zify_cond K3.
        * (* [comment removed for export] *)
          assert (V20 : v2 = 0) by (eapply strncmp_reg_zero; [exact V2| exact K3]).
          assert (PFX1 : firstn (Z.to_nat 11) bs' = firstn (Z.to_nat 11) pem_begin_str).
          { eapply strncmp_model_zero_prefix; [rewrite <- V10; exact V1| clear; lia| rewrite pem_begin_len; clear; lia| intros j b Hj Hb; exact (pem_begin_nonul j b Hj Hb)]. }
          change (Z.to_nat 11) with 11%nat in PFX1. rewrite (firstn_all2 (n := 11%nat) pem_begin_str) in PFX1 by (rewrite pem_begin_len; clear; lia).
          assert (PFX2 : firstn (Z.to_nat 6) (skipn (Z.to_nat (len' - 6)) bs') = firstn (Z.to_nat 6) pem_tail6_str).
          { eapply strncmp_model_zero_prefix; [rewrite <- V20; exact V2| clear; lia| rewrite pem_tail6_len; clear; lia| intros j b Hj Hb; exact (pem_tail6_nonul j b Hj Hb)]. }
          change (Z.to_nat 6) with 6%nat in PFX2. rewrite (firstn_all2 (n := 6%nat) pem_tail6_str) in PFX2 by (rewrite pem_tail6_len; clear; lia).
          pose proof (pem_begin_tail_17 bs' len' L6 ltac:(rewrite LBS1; clear; lia) PFX1 PFX2) as L17.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => sync_at mx ql RL2 LO SLO SPR end. chere. unfold hideP in ELB.
          replace (LB1 + len' + -6) with (LB1 + len' - 6) by (clear; lia).
          lazymatch goal with COM2 : pem_com _ en s LBc Lc f ?mx off rem rA rB rBig, ER2 : _ (e_E en) [] ?mx, MBT2 : mbio_rep ?mx LBc Lc KX _ _ _ _ _, MBO2 : mbio_rep ?mx LBc Lc KY _ _ _ _ _,
                               LOCx : rw_cells usegs ?mx (bv_unsigned (e_sp en) + -208) _, OUTx : rw_cells usegs ?mx (bv_unsigned (e_sp en)) _, LBCx : rw_cells usegs ?mx LB1 _ |- _ =>
          eapply (NAMEP en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 l4 l5 l11 ta tb ql LB1 hBv dBv len' bs' KX KY methX methY);
            [exact COM2| exact ER2| exact REM| exact BOFF| exact BLEN| exact RA6| exact RB5| exact RBIG6| unfold pem_loc; exact LOCx| exact OWNL| exact LBS1| exact LBCx
            | clear - L17 LEN LEN'; lia| exact MBT2| exact KXN| exact MBO2| exact KYN| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUTx] end.
        * (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => sync_at mx ql RL2 LO SLO SPR end. chere. unfold hideP in ELB.
          lazymatch goal with COM2 : pem_com _ en s LBc Lc f ?mx off rem rA rB rBig, ER2 : _ (e_E en) [] ?mx, MBT2 : mbio_rep ?mx LBc Lc KX _ _ _ _ _, MBO2 : mbio_rep ?mx LBc Lc KY _ _ _ _ _,
                               LOCx : rw_cells usegs ?mx (bv_unsigned (e_sp en) + -208) _, OUTx : rw_cells usegs ?mx (bv_unsigned (e_sp en)) _, LBCx : rw_cells usegs ?mx LB1 _ |- _ =>
          eapply (GNGP en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 l4 l5 l11 ta tb ql LB1 hBv dBv fl bs' KX KY methX methY);
            [exact MEAS| exact COM2| exact ER2| exact REM| exact BOFF| exact BLEN| exact RA6| exact RB5| exact RBIG6| unfold pem_loc; exact LOCx| exact OWNL| exact LBS1| exact LBCx
            | exact FL| exact MBT2| exact KXN| exact MBO2| exact KYN| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUTx] end.
  Qed.
End W3.
