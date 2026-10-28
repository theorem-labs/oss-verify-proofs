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
     Fz_W3_endl Fz_W3_hdg Fz_W3_rzt F_memcpy.
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

  Local Notation com_callI := (com_call libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation com_segI := (com_seg libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation er0_callI' := (er0_call errst_at_rest errst_fp errst_rest_agree errst_fp_where).
  Local Notation er0_segI := (er0_seg errst_at_rest errst_fp errst_rest_agree errst_fp_where).

  Lemma first_nul_split : forall (z : byte) (l : list byte), In z l -> exists a b, l = a ++ z :: b /\ ~ In z a.
  Proof.
    intros z l. induction l as [|x l IH]; intros H; [destruct H|].
    destruct (decide (x = z)) as [->|NE].
    - exists [], l. split; [reflexivity| intros []].
    - destruct H as [E|H]; [exfalso; exact (NE E)|]. destruct (IH H) as (a & b & -> & NA). exists (x :: a), b. split; [reflexivity|].
      intros [E|X]; [exact (NE E)| exact (NA X)].
  Qed.

  Lemma t_addiw_small : forall z c, 0 <= z + c < 2 ^ 31 -> 0 <= z < 2 ^ 64 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + c) = z + c.
  Proof.
    intros z c Hz Hr. rewrite unsigned_lit by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31). rewrite Z.mod_small by lia. lia.
  Qed.

  Theorem NAME_proof : pem_malloc_stmt -> pem_free_stmt -> NGETS_stmt libenv errst_at_rest errst_live -> NAME_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros PM PF NGP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l11 ta tb
           ql LB1 hBv dBv len' bs KX KY methX methY.
    cbv zeta. intros COM ER0 REM BOFF BLEN RA6 RB5 RBIG6 LOC OWNL LBS LBC LEN' MBT KXN MBO KYN ELB CFRESH EL NDT OUT.
    unfold NGETS_stmt, J_NGETS in NGP. unfold pem_malloc_stmt in PM. unfold pem_free_stmt in PF.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_NAME, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (RL1 & _ & _ & RL2 & _).
    unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RL2.
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    assert (IDS : forall q, In q (mbio_blocks KX ++ mbio_blocks KY ++ [ql]) \/ q = e_pe en \/ In q (mbio_blocks (e_K en)) -> In q (map blk_id LBc)).
    { destruct MBT as [BMX0 MBX0]. destruct MBO as [BMY0 MBY0]. intros q [X|[->|X]].
      - apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBX0 X)|].
        apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBY0 X)|].
        destruct X as [<-|[]]. exact (cown_id _ _ _ _ _ _ OWNL).
      - apply in_map_iff. exists (e_pe en, e_E en, 904). split; [reflexivity| exact INE].
      - apply mbio_T_blocks in X. apply EK in X. apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. exact (PLB _ Hb). }
    set (nn := len' - 16) in *.
    pose proof (w_bounds nn ltac:(clear - LEN'; subst nn; lia)) as WN.
    (* [comment removed for export] *)
    destruct (rw_cells_CB_split_at usegs m LB1 256 bs (Z.to_nat (len' - 6)) ltac:(clear - LEN'; lia) LBC) as [LBa LBb].
    destruct (rw_cells_CB_split_at usegs m (LB1 + Z.of_nat (Z.to_nat (len' - 6))) (256 - Z.to_nat (len' - 6))%nat (skipn (Z.to_nat (len' - 6)) bs) 1 ltac:(clear - LEN'; lia) LBb) as [LBy LBz].
    pose proof (rw_cells_CB_length _ _ _ _ _ LBy) as LY1.
    destruct (firstn 1 (skipn (Z.to_nat (len' - 6)) bs)) as [|by0 [|by1 tl1]] eqn:EY; [cbn in LY1; discriminate| | cbn in LY1; discriminate].
    eapply (th_cells_congr _ _ _ _ [C1 by0]) in LBy; [| reflexivity| reflexivity| cbn; repeat split; auto].
    replace (LB1 + Z.of_nat (Z.to_nat (len' - 6))) with (LB1 + len' - 6) in LBy, LBz by (clear - LEN'; lia).
    clear LBC LBb. hide ELB. hide ROOM. hide CG. hide LBz.
    pose proof (munch_refl [(LB1 + len' - 6, LB1 + len' - 6 + 1)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix.
    remember (LB1 + len' - 6) as HL eqn:EHL.
    ths. rewrite (t_addiw_small len' (-6)) by (clear - LEN'; lia).
    ths. if_cases KC; zify_cond KC. { exfalso. pose proof alloc_ceiling_lt_2p47 as ACL. clear - KC RL1 RL2 LEN' ACL; lia. } clear KC.
    ths. replace (LB1 + (len' + -6)) with HL by (rewrite EHL; clear; lia).
    ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with H : rw_cells usegs m1 HL [C1 _] |- _ => rename H into LBy1 end.
    (* [comment removed for export] *)
    ths. rewrite (t_addiw_small len' (-16)) by (clear - LEN'; lia). replace (len' + -16) with nn by (subst nn; clear; lia).
    ths. ths. ths. ths. ths.
    lazymatch goal with H : stk usegs m1 _ _ |- _ => rename H into ST1 end. lazymatch goal with H : mem_inv usegs m1 |- _ => rename H into MI1 end.
    chere. subst HL.
    assert (HW1 : Forall (wfree LBc (e_lo en) (bv_unsigned (e_sp en) + 32) (fun q : bptr => q <> ql)) [(LB1 + len' - 6, LB1 + len' - 6 + 1)]%Z).
    { apply Forall_cons; [| apply Forall_nil]. right. exists (ql, LB1, 256). split; [exact (proj1 OWNL)|]. split; [intros X; apply X; reflexivity|].
      unfold blk_addr, blk_size; cbn [fst snd]. clear - LEN'; lia. }
    assert (HXB : forall b, In b (e_LBall en) -> blk_id b <> ql) by (intros b Hb E; unfold hideP in CFRESH; apply (CFRESH _ Hb); rewrite E; do 2 (apply in_or_app; right); left; reflexivity).
    assert (HXE : e_pe en <> ql) by (intros E; apply (DJC ql); [do 2 (apply in_or_app; right); left; reflexivity| left; exact E]).
    assert (HXT : forall q, mbio_T KX q -> q <> ql) by (intros q Hq E; subst q; apply (DJX ql); [apply mbio_T_blocks; exact Hq| apply in_or_app; right; left; reflexivity]).
    assert (HXO : forall q, mbio_T KY q -> q <> ql) by (intros q Hq E; subst q; apply (DJY ql); [apply mbio_T_blocks; exact Hq| left; reflexivity]).
    assert (COM1 : pem_com libenv en s LBc Lc f m1 off rem rA rB rBig).
    { eapply (com_segI en s LBc Lc f m off rem rA rB rBig _ m1 (fun q => q <> ql)); [exact COM| exact MU| exact WM| exact MI1| exact ST1| exact HW1| exact HXB| unfold e_PL; cbn [disjoint_from fst snd]; clear - RL2 LO SLO LEN'; lia]. }
    assert (ER1 : errst_at_rest (e_E en) [] m1).
    { eapply (er0_segI _ en m m1) with (EX := fun q => q <> ql) (hi := bv_unsigned (e_sp en) + 32); [exact ER0| exact MU| exact WM| exact CST| exact INE| exact HW1| exact HXE]. }
    assert (MBT1 : mbio_rep m1 LBc Lc KX hBv methX 0 0 0).
    { eapply (mb_seg _ m m1) with (EX := fun q => q <> ql) (hi := bv_unsigned (e_sp en) + 32); [exact MBT| exact CST| exact MU| exact WM| exact HW1| exact HXT]. }
    assert (MBO1 : mbio_rep m1 LBc Lc KY dBv methY 0 0 0).
    { eapply (mb_seg _ m m1) with (EX := fun q => q <> ql) (hi := bv_unsigned (e_sp en) + 32); [exact MBO| exact CST| exact MU| exact WM| exact HW1| exact HXO]. }
    unfold hideP in LBz.
    assert (LBz1 : rw_cells usegs m1 (LB1 + len' - 6 + Z.of_nat 1) [CB (256 - Z.to_nat (len' - 6) - 1) (drop 1 (drop (Z.to_nat (len' - 6)) bs))]).
    { eapply rw_cells_transport; [exact LBz| exact MU| exact WM|]. cbn [disjoint_from cells_size csize fst snd]. clear - LEN'; lia. }
    lazymatch goal with H : rw_cells usegs m1 LB1 _ |- _ => rename H into LBa1 end.
    lazymatch goal with H : rw_cells usegs m1 (bv_unsigned (e_sp en) + -208) _ |- _ => rename H into LOC1 end.
    lazymatch goal with H : rw_cells usegs m1 (bv_unsigned (e_sp en)) _ |- _ => rename H into OUT1 end.
    pose proof COM1 as (CST1 & _). clear COM CST MU WM HP LATCH LXS CIMG LBz MBT MBO ER0. try clear MI. try clear ERR. try clear ST.
    (* [comment removed for export] *)
    assert (LBN1 : rw_cells usegs m1 LB1 [CB (Z.to_nat (len' - 6) + 1)%nat (take (Z.to_nat (len' - 6)) bs ++ [Z_to_bv 8 0])]).
    { eapply rw_cells_CB_join; [exact LBa1|]. replace (LB1 + Z.of_nat (Z.to_nat (len' - 6))) with (LB1 + len' - 6) by (clear - LEN'; lia).
      eapply (th_cells_congr _ _ _ _ [CB 1%nat [Z_to_bv 8 0]]) in LBy1; [exact LBy1| reflexivity| reflexivity| cbn; repeat split; auto]. }
    assert (LBW : rw_cells usegs m1 LB1 [CB 256 ((take (Z.to_nat (len' - 6)) bs ++ [Z_to_bv 8 0]) ++ drop 1 (drop (Z.to_nat (len' - 6)) bs))]).
    { replace 256%nat with ((Z.to_nat (len' - 6) + 1) + (256 - Z.to_nat (len' - 6) - 1))%nat by (clear - LEN'; lia). eapply rw_cells_CB_join; [exact LBN1|].
      replace (LB1 + Z.of_nat (Z.to_nat (len' - 6) + 1)) with (LB1 + len' - 6 + Z.of_nat 1) by (clear - LEN'; lia). exact LBz1. }
    set (bsw := (take (Z.to_nat (len' - 6)) bs ++ [Z_to_bv 8 0]) ++ drop 1 (drop (Z.to_nat (len' - 6)) bs)) in LBW.
    assert (LBSW : length bsw = 256%nat) by (subst bsw; rewrite !length_app, !length_drop, length_take, LBS; cbn [length]; clear - LEN'; lia).
    clear LBa1 LBz1 LBy1.
    (* [comment removed for export] *)
    unfold hideP in ROOM.
    eapply climpl_seq.
    { eapply PM with (n := nn) (flags := e_flags en) (lo := e_lo en) (B := e_B en);
        [clear - FU REM OFF; lia| eapply croom_weaken; [exact ROOM| clear - RA6 WN; lia| clear - RB5 WN; lia| clear - RBIG6 WN LEN' OFF BOFF; subst nn; lia]
        | clear - LEN'; subst nn; lia| clear - FLR; lia| exact CST1| rewrite unsigned_lit by lia; unfold PMAL_STACK, CSM_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia| reflexivity| reflexivity]. }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2' & RET & FU2 & GR2 & CST2 & FRM2 & (qn & NM & njunk & -> & -> & -> & RNN & NMC2)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    assert (COM2 : pem_com libenv en st2 ((qn, NM, nn) :: LBc) ((qn, nn) :: Lc) f2 m2 off (rem - 1) (rA - wA nn) (rB - wB nn) (rBig - wBig nn)).
    { eapply (com_callI en) with (T1 := fun _ => False); [exact COM1| exact CST2| exact FRM2| unfold e_PL; clear; lia| exact FU2| clear - REM OFF; lia| exact GR2| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X];
        clear - RA6 RB5 RBIG6 WN LEN' OFF BOFF; subst nn; lia. }
    pose proof FRM2 as (CFR2 & KP2 & _).
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBT1 FRM2 ltac:(intros q _ X; exact X)) as MBT2. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBO1 FRM2 ltac:(intros q _ X; exact X)) as MBO2.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNL FRM2 ltac:(intros X; exact X)) as OWNL2.
    pose proof (er0_callI' en _ _ _ _ _ _ _ _ _ _ ER1 FRM2 INE ltac:(intros X; exact X)) as ER2.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear; lia)) as LOC2. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OUT1 ltac:(clear; lia)) as OUT2.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ql, LB1, 256) CFR2 LBW (proj1 OWNL) ltac:(intros X; exact X) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as LBW2.
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia.
    pose proof RNN as (NM0 & NM16 & _ & NMCL & _). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in NMCL.
    assert (FRN : forall q A' n', In (q, A', n') LBc -> q <> qn) by (intros q A' n' Hq; exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 Hq)).
    assert (NQN : ~ In qn ((mbio_blocks KX ++ mbio_blocks KY ++ [ql]) ++ e_pe en :: mbio_blocks (e_K en))).
    { intros X. assert (Y : In qn (map blk_id LBc)); [apply IDS; apply in_app_iff in X; destruct X as [X|[X|X]]; [left; exact X| right; left; exact (eq_sym X)| right; right; exact X]|].
      apply in_map_iff in Y. destruct Y as ([[q A'] n'] & E & Hq). cbn in E. exact (FRN _ _ _ Hq E). }
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 (or_introl eq_refl) (or_intror (proj1 OWNL)) ltac:(intros E; apply NQN; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; left; exact (eq_sym E))) as APNL.
    unfold blk_addr, blk_size in APNL. cbn [fst snd] in APNL.
    clear COM1 CST1 ER1 MBT1 MBO1 LOC1 OUT1 LBW LBN1 FRM2 CFR2.
    (* [comment removed for export] *)
    pose proof (rw_cells_bytes_at _ _ _ _ LBW2) as SRCB. cbn [cells_bytes cbytes] in SRCB. rewrite app_nil_r in SRCB.
    rewrite <- (firstn_skipn 11 bsw) in SRCB. apply (proj1 (bytes_at_app _ _ _ _ _)) in SRCB. destruct SRCB as [_ SRCB].
    rewrite firstn_length_le in SRCB by (rewrite LBSW; clear; lia).
    rewrite <- (firstn_skipn (Z.to_nat nn) (skipn 11 bsw)) in SRCB. apply (proj1 (bytes_at_app _ _ _ _ _)) in SRCB. destruct SRCB as [SRC _].
    set (src := take (Z.to_nat nn) (drop 11 bsw)) in SRC.
    assert (LSRC : length src = Z.to_nat nn) by (subst src; rewrite length_take, length_drop, LBSW; clear - LEN'; subst nn; lia).
    assert (SRCNUL : In (Z_to_bv 8 0) src).
    { subst src bsw. rewrite drop_app_le by (rewrite length_app, length_take, LBS; cbn [length]; clear - LEN'; lia).
      assert (LD : length (drop 11 (take (Z.to_nat (len' - 6)) bs ++ [Z_to_bv 8 0])) = Z.to_nat nn) by (rewrite length_drop, length_app, length_take, LBS; cbn [length]; clear - LEN'; subst nn; lia).
      rewrite <- LD, take_app_length. rewrite drop_app_le by (rewrite length_take, LBS; clear - LEN'; lia). apply in_or_app; right; left; reflexivity. }
    replace (LB1 + Z.of_nat 11) with (LB1 + 11) in SRC by (clear; lia).
    pose proof (munch_refl [(NM, NM + nn); (bv_unsigned (e_sp en) + -192, bv_unsigned (e_sp en) + -184)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by (clear - NM0 NMCL LO SLO SPR; lia). clear - K0 NM0. lia. }
    ths. ths. if_cases KC; zify_cond KC. { exfalso. pose proof alloc_ceiling_lt_2p47 as ACL. clear - KC RL1 RL2 ACL; lia. } clear KC.
    ths. ths. ths. ths.
    tcall (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src njunk).
    all: try first [eassumption | clear - NM0 NMCL RL1 RL2 LO SLO SPR LEN' APNL LSRC; subst nn; lia].
    cbv beta delta [mkR].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    lazymatch goal with H : rw_cells usegs m3 NM [CB _ src] |- _ => rename H into NMC3 end.
    lazymatch goal with H : stk usegs m3 _ _ |- _ => rename H into ST3 end. lazymatch goal with H : mem_inv usegs m3 |- _ => rename H into MI3 end.
    lazymatch goal with H : rw_cells usegs m3 (bv_unsigned (e_sp en) + -208) _ |- _ => rename H into LOC3 end.
    lazymatch goal with H : rw_cells usegs m3 (bv_unsigned (e_sp en)) _ |- _ => rename H into OUT3 end.
    lazymatch goal with H : rw_cells usegs m3 LB1 _ |- _ => rename H into LBW3 end.
    assert (HW3 : Forall (wfree ((qn, NM, nn) :: LBc) (e_lo en) (bv_unsigned (e_sp en) + 32) (fun q : bptr => q <> qn)) [(NM, NM + nn); (bv_unsigned (e_sp en) + -192, bv_unsigned (e_sp en) + -184)]%Z).
    { apply Forall_cons; [| apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]]. right. exists (qn, NM, nn). split; [left; reflexivity|]. split; [intros X; apply X; reflexivity|]. unfold blk_addr, blk_size; cbn [fst snd]. clear; lia. }
    assert (FRB : forall b, In b (e_LBall en) -> blk_id b <> qn) by (intros [[q A'] n'] Hb; exact (FRN _ _ _ (PLB _ Hb))).
    assert (NQE : e_pe en <> qn) by (intros E; apply NQN; apply in_or_app; right; left; exact E).
    assert (NQX : forall q, mbio_T KX q -> q <> qn) by (intros q Hq E; subst q; apply NQN; apply in_or_app; left; apply in_or_app; left; apply mbio_T_blocks; exact Hq).
    assert (NQY : forall q, mbio_T KY q -> q <> qn) by (intros q Hq E; subst q; apply NQN; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact Hq).
    assert (NQL : ql <> qn) by (intros E; apply NQN; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; left; exact E).
    assert (COM3 : pem_com libenv en st2 ((qn, NM, nn) :: LBc) ((qn, nn) :: Lc) f2 m3 off (rem - 1) (rA - wA nn) (rB - wB nn) (rBig - wBig nn)).
    { eapply (com_segI en st2 _ _ f2 m2 off (rem - 1)%nat _ _ _ _ m3 (fun q => q <> qn)); [exact COM2| exact MU| exact WM| exact MI3| exact ST3| exact HW3| exact FRB| unfold e_PL; cbn [disjoint_from fst snd]; clear - NMCL LO SLO; lia]. }
    assert (ER3 : errst_at_rest (e_E en) [] m3).
    { eapply (er0_segI _ en m2 m3) with (EX := fun q => q <> qn) (hi := bv_unsigned (e_sp en) + 32); [exact ER2| exact MU| exact WM| exact CST2| right; exact INE| exact HW3| exact NQE]. }
    assert (MBT3 : mbio_rep m3 ((qn, NM, nn) :: LBc) ((qn, nn) :: Lc) KX hBv methX 0 0 0).
    { eapply (mb_seg _ m2 m3) with (EX := fun q => q <> qn) (hi := bv_unsigned (e_sp en) + 32); [exact MBT2| exact CST2| exact MU| exact WM| exact HW3| exact NQX]. }
    assert (MBO3 : mbio_rep m3 ((qn, NM, nn) :: LBc) ((qn, nn) :: Lc) KY dBv methY 0 0 0).
    { eapply (mb_seg _ m2 m3) with (EX := fun q => q <> qn) (hi := bv_unsigned (e_sp en) + 32); [exact MBO2| exact CST2| exact MU| exact WM| exact HW3| exact NQY]. }
    pose proof COM3 as (CST3 & _). clear COM2 CST2 ER2 MBT2 MBO2 MU WM.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    (* [comment removed for export] *)
    ths. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply PF with (p := ql) (A := LB1) (n := 256) (nm := 256) (num := 256) (flags := e_flags en) (junk := bsw) (lo := e_lo en) (B := e_B en);
        [clear - FU FU2 REM OFF; lia| exact OWNL2| clear; lia| exact LBW3| clear - FLR; lia| exact CST3| rewrite unsigned_lit by lia; unfold PFREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia
        | reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros f4 L4 st4 ms4 (v4 & m4 & LB4 & RET & FU4 & GR4 & CST4 & FRM4 & (-> & i & HI & ->)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM4 by lia.
    pose proof (w_bounds 256 ltac:(clear; lia)) as (WA & WB' & WAB & WBIG). pose proof (wB_big 256 ltac:(unfold TIER_A_MAX; clear; lia)) as (WA0 & WB1 & WBIG1).
    assert (HT4 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ ql = q).
    { intros q [Hq|Hq] _ <-; apply in_map_iff in Hq; unfold hideP in CFRESH.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. do 2 (apply in_or_app; right). left; reflexivity.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). do 2 (apply in_or_app; right). left; reflexivity. }
    assert (HK4 : forall q, mbio_T (e_K en) q -> ~ ql = q) by (intros q Hq <-; apply (DJC ql); [do 2 (apply in_or_app; right); left; reflexivity| right; apply mbio_T_blocks; exact Hq]).
    assert (COM4 : pem_com libenv en st4 (lb_remove ql ((qn, NM, nn) :: LBc)) (cremove i ((qn, nn) :: Lc)) f4 m4 off (rem - 2) (rA - wA nn) (rB - wB nn + 1) (rBig - wBig nn + 8448)).
    { eapply (com_callI en) with (T1 := eq ql); [exact COM3| exact CST4| exact FRM4| unfold e_PL; clear; lia| exact FU4| clear - REM OFF; lia| exact GR4| | | | | | | exact HT4| exact HK4| intros E; exact (HXE (eq_sym E))];
        rewrite ?WA0, ?WB1, ?WBIG1; clear - RA6 RB5 RBIG6 WN RA0 RB0 RBIG0 LEN' OFF BOFF; subst nn; lia. }
    pose proof FRM4 as (CFR4 & KP4 & _).
    assert (HX4 : forall q, mbio_T KX q -> ~ ql = q) by (intros q Hq E; exact (HXT _ Hq (eq_sym E))).
    assert (HY4 : forall q, mbio_T KY q -> ~ ql = q) by (intros q Hq E; exact (HXO _ Hq (eq_sym E))).
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBT3 FRM4 HX4) as MBT4. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBO3 FRM4 HY4) as MBO4.
    assert (OWNN3 : cown ((qn, NM, nn) :: LBc) ((qn, nn) :: Lc) qn NM nn nn) by (split; left; reflexivity).
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN3 FRM4 NQL) as OWNN4.
    pose proof (er0_callI' en _ _ _ _ _ _ _ _ _ _ ER3 FRM4 (or_intror INE) ltac:(intros E; exact (HXE (eq_sym E)))) as ER4.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 LOC3 ltac:(clear; lia)) as LOC4. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 OUT3 ltac:(clear; lia)) as OUT4.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, NM, nn) CFR4 NMC3 (or_introl eq_refl) NQL ltac:(cbn; clear; lia) ltac:(cbn; clear - LEN'; subst nn; lia)) as NMC4.
    pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & _ & MI4 & _) & _). rewrite unsigned_lit in ST4 by lia.
    pose proof COM4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ROOM4 & _).
    clear COM3 CST3 ER3 MBT3 MBO3 LOC3 OUT3 NMC3 LBW3 FRM4 CFR4 MU WM MI3 ST3.
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply PM with (n := 256) (flags := e_flags en) (lo := e_lo en) (B := e_B en);
        [clear - FU FU2 FU4 REM OFF; lia| eapply croom_weaken; [exact ROOM4| clear - RA6 WN WA; lia| clear - RB5 WN WB'; lia| clear - RBIG6 WN WBIG LEN' OFF BOFF; subst nn; lia]
        | clear; lia| clear - FLR; lia| exact CST4| rewrite unsigned_lit by lia; unfold PMAL_STACK, CSM_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia| reflexivity| reflexivity]. }
    cbv beta. intros f5 L5 st5 ms5 (v5 & m5 & LB5 & RET & FU5 & GR5 & CST5 & FRM5 & (ql2 & LB2 & ljunk & -> & -> & -> & RNL & LBC5)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM5 by lia.
    assert (COM5 : pem_com libenv en st5 ((ql2, LB2, 256) :: lb_remove ql ((qn, NM, nn) :: LBc)) ((ql2, 256) :: cremove i ((qn, nn) :: Lc)) f5 m5 off (rem - 3) (rA - wA nn) (rB - wB nn) (rBig - wBig nn)).
    { eapply (com_callI en) with (T1 := fun _ => False); [exact COM4| exact CST5| exact FRM5| unfold e_PL; clear; lia| exact FU5| clear - REM OFF; lia| exact GR5| | | | | | | intros q _ _ X; exact X| intros q _ X; exact X| intros X; exact X];
        rewrite ?WA0, ?WB1, ?WBIG1; clear - RA6 RB5 RBIG6 WN RA0 RB0 RBIG0 LEN' OFF BOFF; subst nn; lia. }
    pose proof FRM5 as (CFR5 & KP5 & _).
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBT4 FRM5 ltac:(intros q _ X; exact X)) as MBT5. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBO4 FRM5 ltac:(intros q _ X; exact X)) as MBO5.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN4 FRM5 ltac:(intros X; exact X)) as OWNN5.
    assert (INE4 : In (e_pe en, e_E en, 904) (lb_remove ql ((qn, NM, nn) :: LBc))) by (apply lb_remove_In; split; [right; exact INE| unfold blk_id; cbn [fst]; exact HXE]).
    pose proof (er0_callI' en _ _ _ _ _ _ _ _ _ _ ER4 FRM5 INE4 ltac:(intros X; exact X)) as ER5.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR5 LOC4 ltac:(clear; lia)) as LOC5. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR5 OUT4 ltac:(clear; lia)) as OUT5.
    assert (INN4 : In (qn, NM, nn) (lb_remove ql ((qn, NM, nn) :: LBc))) by (apply lb_remove_In; split; [left; reflexivity| unfold blk_id; cbn [fst]; intros E; exact (NQL (eq_sym E))]).
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, NM, nn) CFR5 NMC4 INN4 ltac:(intros X; exact X) ltac:(cbn; clear; lia) ltac:(cbn; clear - LEN'; subst nn; lia)) as NMC5.
    pose proof CST5 as (HP5 & _ & (errv5 & _ & _ & ST5 & _ & _ & MI5 & _) & _). rewrite unsigned_lit in ST5 by lia.
    pose proof RNL as (LB20 & _ & _ & LB2CL & _). unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in LB2CL.
    pose proof (rw_cells_CB_length _ _ _ _ _ LBC5) as LBS5.
    assert (FRL : forall q A' n', In (q, A', n') (lb_remove ql ((qn, NM, nn) :: LBc)) -> q <> ql2) by (intros q A' n' Hq; exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST5 Hq)).
    clear COM4 CST4 ER4 MBT4 MBO4 LOC4 OUT4 NMC4 FRM5 CFR5 MU WM MI4 ST4.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    (* [comment removed for export] *)
    cprefix. ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by (clear - LB20 LB2CL LO SLO SPR; lia). clear - K1 LB20. lia. }
    ths. chere.
    (* [comment removed for export] *)
    destruct (first_nul_split _ _ SRCNUL) as (str & bn2 & ESRC & NONUL).
    assert (LBN : length (str ++ Z_to_bv 8 0 :: bn2) = Z.to_nat nn) by (rewrite <- ESRC; exact LSRC). rewrite ESRC in NMC5.
    unfold hideP in ELB, CFRESH.
    assert (REM5 : (Z.to_nat (2 * (e_blen en - off) + 16) <= rem - 3)%nat) by (clear - REM OFF; lia).
    assert (RA5 : 5 <= rA - wA nn) by (clear - RA6 WN; lia). assert (RB4 : 4 <= rB - wB nn) by (clear - RB5 WN; lia).
    assert (RBIG5 : 6 * (e_blen en - e_boff en) + 32778 <= rBig - wBig nn) by (clear - RBIG6 WN LEN'; subst nn; lia).
    assert (NN : 1 <= nn <= 239) by (clear - LEN'; subst nn; lia).
    assert (OWNL5 : cown ((ql2, LB2, 256) :: lb_remove ql ((qn, NM, nn) :: LBc)) ((ql2, 256) :: cremove i ((qn, nn) :: Lc)) ql2 LB2 256 256) by (split; left; reflexivity).
    (* [comment removed for export] *)
    assert (INLB : forall q, In q ((mbio_blocks KX ++ mbio_blocks KY) ++ e_pe en :: mbio_blocks (e_K en)) -> exists A' n', In (q, A', n') (lb_remove ql ((qn, NM, nn) :: LBc))).
    { intros q X. assert (Y : In q (map blk_id LBc)).
      { apply IDS. apply in_app_iff in X. destruct X as [X|[X|X]]; [left; rewrite app_assoc; apply in_or_app; left; exact X| right; left; exact (eq_sym X)| right; right; exact X]. }
      assert (NQ : q <> ql).
      { intros ->. apply in_app_iff in X. destruct X as [X|[X|X]]; [| exact (HXE X)|].
        - apply in_app_iff in X. destruct X as [X|X]; [apply (DJX ql X); apply in_or_app; right; left; reflexivity| apply (DJY ql X); left; reflexivity].
        - apply (DJC ql); [do 2 (apply in_or_app; right); left; reflexivity| right; exact X]. }
      apply in_map_iff in Y. destruct Y as ([[q' A'] n'] & E & Hb). cbn in E. subst q'. exists A', n'. apply lb_remove_In. split; [right; exact Hb| unfold blk_id; cbn [fst]; exact NQ]. }
    eapply (NGP en st5 _ _ f5 m5 off (rem - 3)%nat (rA - wA nn) (rB - wB nn) (rBig - wBig nn) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              qn ql2 NM nn LB2 hBv dBv str bn2 ljunk KX KY methX methY);
      [exact COM5| exact ER5| exact REM5| exact BOFF| exact BLEN| exact RA5| exact RB4| exact RBIG5| unfold pem_loc; exact LOC5| exact OWNN5| exact NN| exact LBN| exact NMC5| exact NONUL
      | exact OWNL5| exact LBS5| exact LBC5| exact MBT5| exact KXN| exact MBO5| exact KYN| | | | | exact OUT5].
    - intros b [<-|Hb]; [right; unfold blk_id; cbn [fst]; rewrite !in_app_iff; cbn [In]; tauto|].
      apply lb_remove_In in Hb. destruct Hb as [[<-|Hb] NE]; [right; unfold blk_id; cbn [fst]; rewrite !in_app_iff; cbn [In]; tauto|].
      destruct (ELB _ Hb) as [X|X]; [left; exact X| right]. rewrite !in_app_iff in X |- *. cbn [In] in X |- *. clear - X NE. intuition congruence.
    - intros b Hb X. apply in_app_iff in X. destruct X as [X|X]; [apply (CFRESH _ Hb); apply in_or_app; left; exact X|].
      apply in_app_iff in X. destruct X as [X|X]; [apply (CFRESH _ Hb); apply in_or_app; right; apply in_or_app; left; exact X|].
      destruct X as [X|[X|[]]]; [exact (FRB _ Hb (eq_sym X))|].
      destruct b as [[q A'] n']. refine (FRL _ _ _ _ (eq_sym X)). apply lb_remove_In. split; [right; exact (PLB _ Hb)| exact (HXB _ Hb)].
    - intros q nm Hq X.
      assert (HB : exists A' n', In (q, A', n') LBc).
      { destruct CO as (CLB & PERM & IDS0). assert (Z1 : In q (map fst Lc)) by (apply in_map_iff; exists (q, nm); split; [reflexivity| exact (PLC _ _ Hq)]).
        rewrite <- IDS0 in Z1. apply in_map_iff in Z1. destruct Z1 as ([[q' A'] n'] & E & Hb). cbn in E. subst q'. exists A', n'.
        eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; left; exact Hb]. }
      destruct HB as (A' & n' & Hb).
      apply in_app_iff in X. destruct X as [X|X]; [apply (EL _ _ Hq); apply in_or_app; left; exact X|].
      apply in_app_iff in X. destruct X as [X|X]; [apply (EL _ _ Hq); apply in_or_app; right; apply in_or_app; left; exact X|].
      destruct X as [X|[X|[]]]; [exact (FRN _ _ _ Hb (eq_sym X))|].
      refine (FRL _ _ _ _ (eq_sym X)). apply lb_remove_In. split; [right; exact Hb|]. unfold blk_id; cbn [fst]. intros E. apply (EL _ _ Hq). do 2 (apply in_or_app; right). left. exact (eq_sym E).
    - lazymatch goal with |- List.NoDup ?l => replace l with ((mbio_blocks KX ++ mbio_blocks KY) ++ qn :: ql2 :: e_pe en :: mbio_blocks (e_K en)) by (rewrite <- ?app_assoc; reflexivity) end.
      assert (ND0 : List.NoDup ((mbio_blocks KX ++ mbio_blocks KY) ++ e_pe en :: mbio_blocks (e_K en))).
      { apply (nd_drop _ _ ql). lazymatch goal with |- List.NoDup ?l => replace l with ((mbio_blocks KX ++ mbio_blocks KY ++ [ql]) ++ e_pe en :: mbio_blocks (e_K en)); [exact NDT| rewrite <- ?app_assoc; reflexivity] end. }
      apply nd_insert2; [exact ND0| | |].
      + intros X. apply NQN. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left| right; exact X]. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right; apply in_or_app; left; exact X].
      + intros X. destruct (INLB _ X) as (A' & n' & Hb). exact (FRL _ _ _ Hb eq_refl).
      + intros E. exact (FRL _ _ _ INN4 E).
  Qed.
End W3.
