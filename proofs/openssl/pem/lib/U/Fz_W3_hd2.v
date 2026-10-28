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
     Fz_W3_endl Fz_W3_hd1 F_strncmp.
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

  Lemma ow_bounds' : forall K mx, 0 <= mx -> 0 <= owA K mx <= 1 /\ 0 <= owB K mx <= 1 /\ 0 <= owBig K mx <= mx + 8192.
  Proof. intros K mx H. unfold owA, owB, owBig. destruct (k_d K); [pose proof (w_bounds mx H); lia| lia]. Qed.

  (* [comment removed for export] *)
  Theorem HD2_proof : forall N,
    sanitize_line_stmt -> ENDLINE_stmt libenv errst_at_rest errst_live -> RAISE2_stmt libenv errst_at_rest errst_live ->
    GETS2_at libenv errst_at_rest errst_live N -> PUTS_at libenv errst_at_rest errst_live N -> HD2_at libenv errst_at_rest errst_live N.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros N SAN ENDLP RAISEP G2P PUTSP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 l1 l7 l9 ta tb
           qn ql namev nn LB2 hBv dBv tmpv ov got prev endv partv fl2 len str bn2 bs KT KO methT methO lenT maxT lenO maxO.
    intros MEAS COM INV LOC ENDV PREV PARTV FL2.
    unfold sanitize_line_stmt in SAN. unfold ENDLINE_stmt, J_ENDLINE in ENDLP. unfold RAISE2_stmt, J_RAISE2 in RAISEP. unfold GETS2_at, J_GETS2 in G2P. unfold PUTS_at, J_PUTS in PUTSP.
    pose proof INV as ((ER0 & BLEN & SA & SB & SBIG & MAXT & MAXO & DNT & DNO & GOT & ROLE & OWNN & NN & LBN & NMC & NONUL & OWNL & LBS & LBC
                      & MBT & MBO & ELB & CFRESH & EL & NDT & OUT) & REM & LSUM & LEN & NULk).
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_HD2, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (RL1 & _ & _ & RL2 & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RL2, RN2.
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    inversion NDC3 as [|z1 k1 NQ1 ND4]; subst. cbn [In] in NQ1.
    assert (HN1 : qn <> ql) by (clear - NQ1; intros E; apply NQ1; left; exact (eq_sym E)).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN) (proj1 OWNL) HN1) as ANL.
    assert (LTO : 0 <= lenT <= maxT /\ 0 <= lenO <= maxO).
    { destruct MBT as (BMt & BBt & RPt & flt & rrwt & padwt & nrt & nwt & _ & _ & _ & _ & _ & _ & _ & (rmaxwt & _ & _ & _ & _ & X1 & X2 & X3 & _)).
      destruct MBO as (BMo & BBo & RPo & flo & rrwo & padwo & nro & nwo & _ & _ & _ & _ & _ & _ & _ & (rmaxwo & _ & _ & _ & _ & Y1 & Y2 & Y3 & _)). clear - X1 X2 X3 Y1 Y2 Y3. lia. }
    pose proof (ow_bounds' KT maxT ltac:(clear - LTO; lia)) as OWT. pose proof (ow_bounds' KO maxO ltac:(clear - LTO; lia)) as OWO.
    assert (NUL : In (Z_to_bv 8 0) (str ++ Z_to_bv 8 0 :: bn2)) by (apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (HWs : Forall (wfree LBc (e_lo en) (bv_unsigned (e_sp en) + 32) (fun q : bptr => q <> ql))
                    [(bv_unsigned (e_sp en) + -208 - 112, bv_unsigned (e_sp en) + -208); (LB2, LB2 + 256); (bv_unsigned (e_sp en) + -208, bv_unsigned (e_sp en) + -176)]%Z).
    { apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia|]. apply Forall_cons; [| apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]].
      right. exists (ql, LB2, 256). split; [exact (proj1 OWNL)|]. split; [intros X; apply X; reflexivity|]. unfold blk_addr, blk_size; cbn [fst snd]. clear; lia. }
    assert (HXT : forall q, mbio_T KT q -> q <> ql) by (intros q Hq E; subst q; apply (DJX ql); [apply mbio_T_blocks; exact Hq| apply in_or_app; right; right; left; reflexivity]).
    assert (HXO : forall q, mbio_T KO q -> q <> ql) by (intros q Hq E; subst q; apply (DJY ql); [apply mbio_T_blocks; exact Hq| right; left; reflexivity]).
    assert (HXE : e_pe en <> ql) by (intros E; apply (DJC ql); [do 2 (apply in_or_app; right); right; left; reflexivity| left; exact E]).
    assert (HXB : forall b, In b (e_LBall en) -> blk_id b <> ql) by (intros b Hb E; apply (CFRESH _ Hb); rewrite E; do 2 (apply in_or_app; right); right; left; reflexivity).
    hide ROLE. hide ELB. hide ROOM. hide CG.
    pose proof (munch_refl [(bv_unsigned (e_sp en) + -208 - 112, bv_unsigned (e_sp en) + -208); (LB2, LB2 + 256); (bv_unsigned (e_sp en) + -208, bv_unsigned (e_sp en) + -176)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut;
      [ eapply (SAN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LB2 len fl2 0 (e_lo en) bs);
        [ reflexivity| reflexivity| reflexivity| reflexivity| exact RL1| exact RL2| exact LEN| exact FL2| clear; lia| exact LBS| exact LBC| exact NULk
        | rewrite unsigned_lit by (clear - SPR SLO LO GLO; lia); exact ST| exact LO| rewrite unsigned_lit by (clear - SPR SLO LO GLO; lia); unfold SAN_STACK; clear - SLO; lia| exact MI ]
      | ]
    end.
    cbv beta. intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & len' & bs' & m1 & -> & LEN' & MU1 & WM1 & MI1 & ST1 & LBS1 & LBC1 & NL1 & NUL1).
    rewrite !unsigned_lit in MU1 by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in ST1 by (clear - SPR SLO LO GLO; lia). th_ret_lit.
    replace (bv_unsigned (e_sp en) + -208 - 112) with (bv_unsigned (e_sp en) + -208 + -112) in MU by (clear; lia).
    replace (bv_unsigned (e_sp en) + -208 - 112) with (bv_unsigned (e_sp en) + -208 + -112) in HWs by (clear; lia).
    clear LBC. transport_after_call usegs m m1 MU1 WM1. clear MU1 WM1 MI. try clear ST.
    (* [comment removed for export] *)
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
    destruct (nth_error bs' 0%nat) as [b0|] eqn:Hb0; [| exfalso; apply nth_error_None in Hb0; rewrite LBS1 in Hb0; clear - Hb0; lia].
    pose proof (u8arr_read usegs m1 LB2 bs' 0 b0 (Z_to_bv 64 (LB2 + 0)) (u8arr_of_rw_cells _ _ _ _ _ LBC1) Hb0 ltac:(clear; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    zstep. clear RD. ths. ths. ths. ths. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      zstep. ths. ths. if_cases KP; zify_cond KP.
      + (* [comment removed for export] *)
        ths. ths. ths. ths. if_cases KG; zify_cond KG.
        * (* [comment removed for export] *)
          ths. ths. ths. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => sync_at mx ql RL2 LO SLO SPR end. chere. unfold hideP in ROLE, ELB.
          assert (G2 : got = 2) by (rewrite ?unsigned_lit in KG by (clear - GOT; lia); clear - KG GOT; lia).
          destruct ROLE as [(RG & _ & _)|(RG & -> & ->)]; [exfalso; exact (RG G2)|].
          lazymatch goal with COM2 : pem_com _ en s LBc Lc f ?mx off rem rA rB rBig, ER2 : _ (e_E en) [] ?mx, MBT2 : mbio_rep ?mx LBc Lc KT _ _ _ _ _, MBO2 : mbio_rep ?mx LBc Lc KO _ _ _ _ _,
                               LOCx : rw_cells usegs ?mx (bv_unsigned (e_sp en) + -208) _, OUTx : rw_cells usegs ?mx (bv_unsigned (e_sp en)) _, NMCx : rw_cells usegs ?mx namev _,
                               LBCx : rw_cells usegs ?mx LB2 _ |- _ =>
          eapply (RAISEP en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    qn ql namev nn LB2 hBv dBv 883 (str ++ Z_to_bv 8 0 :: bn2) bs' KO KT methO methT lenO maxO lenT maxT);
            [exact COM2| exact ER2| clear - REM OFF; lia| clear - SA OWT OWO; lia| clear; lia| unfold pem_loc; exact LOCx| exact OWNN| clear - NN; lia| exact LBN| exact NMCx| exact NUL
            | exact OWNL| exact LBS1| exact LBCx| exact MBO2| exact MBT2| | | | | exact OUTx] end.
          -- intros b Hb. destruct (ELB _ Hb) as [X|X]; [left; exact X| right]. rewrite !in_app_iff in X |- *. clear - X. tauto.
          -- intros b Hb X. apply (CFRESH _ Hb). rewrite !in_app_iff in X |- *. clear - X. tauto.
          -- intros q nm Hq X. apply (EL _ _ Hq). rewrite !in_app_iff in X |- *. clear - X. tauto.
          -- eapply Permutation_NoDup; [| exact NDT]. apply Permutation_app_tail. rewrite (app_assoc (mbio_blocks KT)), (app_assoc (mbio_blocks KO)).
             apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl].
        * (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => sync_at mx ql RL2 LO SLO SPR end. chere. unfold hideP in ROLE, ELB.
          assert (G2 : got <> 2) by (rewrite ?unsigned_lit in KG by (clear - GOT; lia); clear - KG GOT; lia).
          destruct ROLE as [(RG & -> & ->)|(RG & _ & _)]; [| exfalso; exact (G2 RG)].
          assert (ELB' : forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) (mbio_blocks KO ++ mbio_blocks KT ++ [qn; ql])).
          { intros b Hb. destruct (ELB _ Hb) as [X|X]; [left; exact X| right]. rewrite !in_app_iff in X |- *. clear - X. tauto. }
          assert (CFRESH' : forall b, In b (e_LBall en) -> ~ In (blk_id b) (mbio_blocks KO ++ mbio_blocks KT ++ [qn; ql])).
          { intros b Hb X. apply (CFRESH _ Hb). rewrite !in_app_iff in X |- *. clear - X. tauto. }
          assert (EL' : forall q nm, In (q, nm) (e_L en) -> ~ In q (mbio_blocks KO ++ mbio_blocks KT ++ [qn; ql])).
          { intros q nm Hq X. apply (EL _ _ Hq). rewrite !in_app_iff in X |- *. clear - X. tauto. }
          assert (NDT' : List.NoDup ((mbio_blocks KO ++ mbio_blocks KT ++ [qn; ql]) ++ e_pe en :: mbio_blocks (e_K en))).
          { eapply Permutation_NoDup; [| exact NDT]. apply Permutation_app_tail. rewrite (app_assoc (mbio_blocks KT)), (app_assoc (mbio_blocks KO)).
            apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl]. }
          assert (SA' : 5 <= rA + owA KO maxO + owA KT maxT) by (clear - SA; lia). assert (SB' : 4 <= rB + owB KO maxO + owB KT maxT) by (clear - SB; lia).
          assert (SBIG' : 6 * (e_blen en - e_boff en) + 32778 <= rBig + owBig KO maxO + owBig KT maxT) by (clear - SBIG; lia).
          assert (GOT2 : 0 <= 2 <= 2) by (clear; lia). assert (ROLE2 : (2 <> 2 /\ dBv = hBv /\ hBv = dBv) \/ (2 = 2 /\ dBv = dBv /\ hBv = hBv)) by (right; repeat split; reflexivity).
          assert (REM2 : (Z.to_nat (2 * (e_blen en - off) + 16) <= rem)%nat) by (clear - REM OFF; lia). assert (LSUM2 : lenO + lenT <= 2 * (off - e_boff en)) by (clear - LSUM LEN; lia).
          lazymatch goal with COM2 : pem_com _ en s LBc Lc f ?mx off rem rA rB rBig, ER2 : _ (e_E en) [] ?mx, MBT2 : mbio_rep ?mx LBc Lc KT _ _ _ _ _, MBO2 : mbio_rep ?mx LBc Lc KO _ _ _ _ _,
                               LOCx : rw_cells usegs ?mx (bv_unsigned (e_sp en) + -208) _, OUTx : rw_cells usegs ?mx (bv_unsigned (e_sp en)) _, NMCx : rw_cells usegs ?mx namev _,
                               LBCx : rw_cells usegs ?mx LB2 _ |- _ =>
          eapply (G2P en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ qn ql namev nn LB2 hBv dBv dBv hBv 2 endv partv str bn2 bs' KO KT methO methT lenO maxO lenT maxT);
            [exact MEAS| exact COM2| | unfold pem_loc; exact LOCx| exact ENDV| exact PARTV];
          unfold gets_pre; split; [hd_core_by ER2 BLEN SA' SB' SBIG' MAXO MAXT DNO DNT GOT2 ROLE2 OWNN NN LBN NMCx NONUL OWNL LBS1 LBCx MBO2 MBT2 ELB' CFRESH' EL' NDT' OUTx| split; [exact REM2| exact LSUM2]]
          end.
      + (* [comment removed for export] *)
        ths. ths. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => sync_at mx ql RL2 LO SLO SPR end. chere. unfold hideP in ROLE, ELB.
        assert (REM2 : (Z.to_nat (2 * (e_blen en - off) + 16) <= rem)%nat) by (clear - REM OFF; lia). assert (LSUM2 : lenT + lenO <= 2 * (off - e_boff en)) by (clear - LSUM LEN; lia).
        lazymatch goal with COM2 : pem_com _ en s LBc Lc f ?mx off rem rA rB rBig, ER2 : _ (e_E en) [] ?mx, MBT2 : mbio_rep ?mx LBc Lc KT _ _ _ _ _, MBO2 : mbio_rep ?mx LBc Lc KO _ _ _ _ _,
                             LOCx : rw_cells usegs ?mx (bv_unsigned (e_sp en) + -208) _, OUTx : rw_cells usegs ?mx (bv_unsigned (e_sp en)) _, NMCx : rw_cells usegs ?mx namev _,
                             LBCx : rw_cells usegs ?mx LB2 _ |- _ =>
        eapply (G2P en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ qn ql namev nn LB2 hBv dBv tmpv ov got endv partv str bn2 bs' KT KO methT methO lenT maxT lenO maxO);
          [exact MEAS| exact COM2| | unfold pem_loc; exact LOCx| exact ENDV| exact PARTV];
        unfold gets_pre; split; [hd_core_by ER2 BLEN SA SB SBIG MAXT MAXO DNT DNO GOT ROLE OWNN NN LBN NMCx NONUL OWNL LBS1 LBCx MBT2 MBO2 ELB CFRESH EL NDT OUTx| split; [exact REM2| exact LSUM2]]
        end.
    - (* [comment removed for export] *)
      ths. ths. ths. ths.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
      assert (ENB : bytes_at usegs m2 0x255f0 pem_end_str) by (apply ro_bytes_at; [exact MI2| clear; lia| rewrite pem_end_len; clear; lia| exact pem_end_ro]).
      pose proof (rw_cells_bytes_at _ _ _ _ LBC1) as LBB2. cbn [cells_bytes cbytes] in LBB2. rewrite app_nil_r in LBB2.
      destruct (strncmp_model_total bs' pem_end_str 9) as (v4 & V4); [clear; lia| rewrite LBS1; clear; lia| rewrite pem_end_len; clear; lia|].
      ths.
      tcall (strncmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs' pem_end_str v4).
      all: try first [eassumption | unfold PEM_ENDSTR; eassumption | clear - RL1 RL2 LO SLO SPR; unfold PEM_ENDSTR; lia].
      cbv beta delta [mkR].
      ths. if_cases KE; zify_cond KE.
      + (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => sync_at mx ql RL2 LO SLO SPR end. chere. unfold hideP in ROLE, ELB.
        assert (RA3 : 3 <= rA) by (clear - SA OWT OWO; lia). assert (RB2 : 2 <= rB) by (clear - SB OWT OWO; lia).
        pose proof (w_bounds (lenT + 1) ltac:(clear - LTO; lia)) as WT1. pose proof (w_bounds (lenO + 1) ltac:(clear - LTO; lia)) as WO1.
        assert (RBIGE : wBig (lenT + 1) + wBig (lenO + 1) <= rBig) by (clear - SBIG OWT OWO WT1 WO1 MAXT MAXO LSUM LEN OFF LTO; lia).
        lazymatch goal with COM2 : pem_com _ en s LBc Lc f ?mx off rem rA rB rBig, ER2 : _ (e_E en) [] ?mx, MBT2 : mbio_rep ?mx LBc Lc KT _ _ _ _ _, MBO2 : mbio_rep ?mx LBc Lc KO _ _ _ _ _,
                             LOCx : rw_cells usegs ?mx (bv_unsigned (e_sp en) + -208) _, OUTx : rw_cells usegs ?mx (bv_unsigned (e_sp en)) _, NMCx : rw_cells usegs ?mx namev _,
                             LBCx : rw_cells usegs ?mx LB2 _ |- _ =>
        destruct ROLE as [(RG & -> & ->)|(RG & -> & ->)];
        [ eapply (ENDLP en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    qn ql namev nn LB2 hBv dBv got str bn2 bs' KT KO methT methO lenT maxT lenO maxO);
            [exact COM2| exact ER2| clear - REM OFF; lia| exact RA3| exact RB2| exact RBIGE| clear - LSUM LEN; lia| unfold pem_loc; exact LOCx| exact GOT| intros; reflexivity| exact OWNN| exact NN| exact LBN
            | exact NMCx| exact NONUL| exact OWNL| exact LBS1| exact LBCx| exact MBT2| exact MBO2| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUTx]
        | eapply (ENDLP en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    qn ql namev nn LB2 hBv dBv got str bn2 bs' KO KT methO methT lenO maxO lenT maxT);
            [exact COM2| exact ER2| clear - REM OFF; lia| exact RA3| exact RB2| clear - RBIGE; lia| clear - LSUM LEN; lia| unfold pem_loc; exact LOCx| exact GOT| intros E; exfalso; clear - E RG; lia| exact OWNN| exact NN| exact LBN
            | exact NMCx| exact NONUL| exact OWNL| exact LBS1| exact LBCx| exact MBO2| exact MBT2| | | | | exact OUTx] ]
        end.
        * intros b Hb. destruct (ELB _ Hb) as [X|X]; [left; exact X| right]. rewrite !in_app_iff in X |- *. clear - X. tauto.
        * intros b Hb X. apply (CFRESH _ Hb). rewrite !in_app_iff in X |- *. clear - X. tauto.
        * intros q nm Hq X. apply (EL _ _ Hq). rewrite !in_app_iff in X |- *. clear - X. tauto.
        * eapply Permutation_NoDup; [| exact NDT]. apply Permutation_app_tail. rewrite (app_assoc (mbio_blocks KT)), (app_assoc (mbio_blocks KO)).
          apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl].
      + (* [comment removed for export] *)
        ths. ths. if_cases KN; zify_cond KN.
        * (* [comment removed for export] *)
          ths. ths. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => sync_at mx ql RL2 LO SLO SPR end. chere. unfold hideP in ROLE, ELB.
          lazymatch goal with COM2 : pem_com _ en s LBc Lc f ?mx off rem rA rB rBig, ER2 : _ (e_E en) [] ?mx, MBT2 : mbio_rep ?mx LBc Lc KT _ _ _ _ _, MBO2 : mbio_rep ?mx LBc Lc KO _ _ _ _ _,
                               LOCx : rw_cells usegs ?mx (bv_unsigned (e_sp en) + -208) _, OUTx : rw_cells usegs ?mx (bv_unsigned (e_sp en)) _, NMCx : rw_cells usegs ?mx namev _,
                               LBCx : rw_cells usegs ?mx LB2 _ |- _ =>
          destruct ROLE as [(RG & -> & ->)|(RG & -> & ->)];
          [ eapply (RAISEP en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                      qn ql namev nn LB2 hBv dBv 907 (str ++ Z_to_bv 8 0 :: bn2) bs' KT KO methT methO lenT maxT lenO maxO);
              [exact COM2| exact ER2| clear - REM OFF; lia| clear - SA OWT OWO; lia| clear; lia| unfold pem_loc; exact LOCx| exact OWNN| clear - NN; lia| exact LBN| exact NMCx| exact NUL
              | exact OWNL| exact LBS1| exact LBCx| exact MBT2| exact MBO2| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUTx]
          | eapply (RAISEP en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                      qn ql namev nn LB2 hBv dBv 907 (str ++ Z_to_bv 8 0 :: bn2) bs' KO KT methO methT lenO maxO lenT maxT);
              [exact COM2| exact ER2| clear - REM OFF; lia| clear - SA OWT OWO; lia| clear; lia| unfold pem_loc; exact LOCx| exact OWNN| clear - NN; lia| exact LBN| exact NMCx| exact NUL
              | exact OWNL| exact LBS1| exact LBCx| exact MBO2| exact MBT2| | | | | exact OUTx] ]
          end.
          -- intros b Hb. destruct (ELB _ Hb) as [X|X]; [left; exact X| right]. rewrite !in_app_iff in X |- *. clear - X. tauto.
          -- intros b Hb X. apply (CFRESH _ Hb). rewrite !in_app_iff in X |- *. clear - X. tauto.
          -- intros q nm Hq X. apply (EL _ _ Hq). rewrite !in_app_iff in X |- *. clear - X. tauto.
          -- eapply Permutation_NoDup; [| exact NDT]. apply Permutation_app_tail. rewrite (app_assoc (mbio_blocks KT)), (app_assoc (mbio_blocks KO)).
             apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl].
        * (* [comment removed for export] *)
          assert (E0 : endv = 0) by (rewrite ?unsigned_lit in KN by (clear - ENDV; lia); clear - KN ENDV; lia).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => sync_at mx ql RL2 LO SLO SPR end. chere. unfold hideP in ROLE, ELB.
          assert (LSUM3 : lenT + lenO + len' <= 2 * (off - e_boff en)) by (clear - LSUM LEN LEN'; lia). assert (LEN3 : 1 <= len' <= 255) by (clear - LEN LEN'; lia).
          lazymatch goal with COM2 : pem_com _ en s LBc Lc f ?mx off rem rA rB rBig, ER2 : _ (e_E en) [] ?mx, MBT2 : mbio_rep ?mx LBc Lc KT _ _ _ _ _, MBO2 : mbio_rep ?mx LBc Lc KO _ _ _ _ _,
                               LOCx : rw_cells usegs ?mx (bv_unsigned (e_sp en) + -208) _, OUTx : rw_cells usegs ?mx (bv_unsigned (e_sp en)) _, NMCx : rw_cells usegs ?mx namev _,
                               LBCx : rw_cells usegs ?mx LB2 _ |- _ =>
          eapply (PUTSP en s LBc Lc f mx off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ qn ql namev nn LB2 hBv dBv tmpv ov got partv len' str bn2 bs' KT KO methT methO lenT maxT lenO maxO);
            [exact MEAS| exact COM2| hd_core_by ER2 BLEN SA SB SBIG MAXT MAXO DNT DNO GOT ROLE OWNN NN LBN NMCx NONUL OWNL LBS1 LBCx MBT2 MBO2 ELB CFRESH EL NDT OUTx
            | exact REM| exact LSUM3| exact LEN3| exact NUL1| unfold pem_loc; exact LOCx| exact PARTV]
          end.
  Qed.
End W3.
