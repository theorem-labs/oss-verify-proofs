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
     Fz_W3_endl Fz_W3_hdg Fz_W3_rzt.
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
  Local Notation er0_segI := (er0_seg errst_at_rest errst_fp errst_rest_agree errst_fp_where).

  Lemma grow_n_le3 : forall x, 0 <= x -> 3 * grow_n x <= 4 * x + 12.
  Proof. intros x Hx. unfold grow_n. Z.div_mod_to_equations. lia. Qed.

  Lemma fst_uniq : forall (L : @clist bptr) (d : bptr) (a b : Z), List.NoDup (map fst L) -> In (d, a) L -> In (d, b) L -> a = b.
  Proof.
    intros L d a b ND. induction L as [|[q nm] L IH]; intros Ha Hb; [destruct Ha|]. cbn [map fst] in ND. inversion ND as [|z l NZ NDL]; subst.
    destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
    - congruence.
    - injection Ha; intros; subst. exfalso. apply NZ. apply in_map_iff. exists (d, b). auto.
    - injection Hb; intros; subst. exfalso. apply NZ. apply in_map_iff. exists (d, a). auto.
    - exact (IH NDL Ha Hb).
  Qed.

  Lemma nodup_mid_ne : forall (l1 l2 : list bptr) (d x : bptr), List.NoDup (l1 ++ d :: l2) -> In x (l1 ++ l2) -> x <> d.
  Proof.
    intros l1 l2 d x ND HX ->. pose proof (nd_split _ _ ND) as (_ & N2 & DJ). apply in_app_iff in HX. destruct HX as [HX|HX].
    - exact (DJ _ HX (or_introl eq_refl)).
    - inversion N2 as [|a l NA _]; subst. exact (NA HX).
  Qed.

  (* [comment removed for export] *)
  Theorem PUTS_proof : forall N, bio_puts_stmt -> FREE2_stmt libenv errst_at_rest errst_live -> GETS1_at libenv errst_at_rest errst_live N ->
    PUTS_at libenv errst_at_rest errst_live N.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros N BP FREE2P G1P en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 l0 l4 l8 l11 ta tb
           qn ql namev nn LB2 hBv dBv tmpv ov got partv len' str bn2 bs KT KO methT methO lenT maxT lenO maxO.
    intros MEAS COM CORE REM LSUM LEN' NULk LOC PARTV. unfold bio_puts_stmt in BP. unfold FREE2_stmt, J_FREE2 in FREE2P. unfold GETS1_at, J_GETS1 in G1P.
    pose proof CORE as (ER0 & BLEN & SA & SB & SBIG & MAXT & MAXO & DNT & DNO & GOT & ROLE & OWNN & NN & LBN & NMC & NONUL & OWNL & LBS & LBC
                      & MBT & MBO & ELB & CFRESH & EL & NDT & OUT).
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_PUTS, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (RL1 & _ & _ & RL2 & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RL2, RN2.
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    inversion NDC3 as [|z1 k1 NQ1 ND4]; subst. cbn [In] in NQ1.
    assert (LTO : 0 <= lenT <= maxT /\ 0 <= lenO <= maxO).
    { destruct MBT as (BMt & BBt & RPt & flt & rrwt & padwt & nrt & nwt & _ & _ & _ & _ & _ & _ & _ & (rmaxwt & _ & _ & _ & _ & X1 & X2 & X3 & _)).
      destruct MBO as (BMo & BBo & RPo & flo & rrwo & padwo & nro & nwo & _ & _ & _ & _ & _ & _ & _ & (rmaxwo & _ & _ & _ & _ & Y1 & Y2 & Y3 & _)). clear - X1 X2 X3 Y1 Y2 Y3. lia. }
    pose proof (ow_bounds KT maxT ltac:(clear - LTO; lia)) as OWT. pose proof (ow_bounds KO maxO ltac:(clear - LTO; lia)) as OWO.
    assert (NUL : In (Z_to_bv 8 0) (str ++ Z_to_bv 8 0 :: bn2)) by (apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    destruct (find_byte 0 bs) as [n0|] eqn:FB.
    2: { exfalso. exact (find_byte_None _ _ FB _ _ NULk eq_refl). }
    destruct (find_byte_Some _ _ _ FB) as (N0L & (bz & BZ & BZ0) & NMIN).
    assert (EBZ : bz = Z_to_bv 8 0) by (apply bv_eq; rewrite BZ0; reflexivity). subst bz.
    assert (N0 : Z.of_nat n0 <= len').
    { destruct (Nat.le_gt_cases n0 (Z.to_nat len')) as [H|H]; [clear - H LEN'; lia|]. exfalso. exact (NMIN _ _ H NULk eq_refl). }
    set (n := Z.of_nat n0) in *.
    assert (NULn : nth_error bs (Z.to_nat n) = Some (Z_to_bv 8 0)) by (subst n; rewrite Nat2Z.id; exact BZ).
    assert (NONULn : forall i, (i < Z.to_nat n)%nat -> nth_error bs i <> Some (Z_to_bv 8 0)).
    { intros i Hi E. subst n. rewrite Nat2Z.id in Hi. apply (NMIN _ _ Hi E). reflexivity. }
    (* [comment removed for export] *)
    assert (HT1 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ mbio_T KT q).
    { intros q [Hq|Hq] _ X; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. apply in_or_app; left. apply mbio_T_blocks. exact X.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). apply in_or_app; left. apply mbio_T_blocks. exact X. }
    assert (HK1 : forall q, mbio_T (e_K en) q -> ~ mbio_T KT q) by (intros q Hq X; apply (DJC q); [apply in_or_app; left; apply mbio_T_blocks; exact X| right; apply mbio_T_blocks; exact Hq]).
    assert (HE1 : ~ mbio_T KT (e_pe en)) by (intros X; apply (DJC (e_pe en)); [apply in_or_app; left; apply mbio_T_blocks; exact X| left; reflexivity]).
    assert (HTO : forall q, mbio_T KO q -> ~ mbio_T KT q) by (intros q Hq X; apply (DJX q); [apply mbio_T_blocks; exact X| apply in_or_app; left; apply mbio_T_blocks; exact Hq]).
    assert (HTN : ~ mbio_T KT qn) by (intros X; apply (DJX qn); [apply mbio_T_blocks; exact X| apply in_or_app; right; left; reflexivity]).
    assert (HTL : ~ mbio_T KT ql) by (intros X; apply (DJX ql); [apply mbio_T_blocks; exact X| apply in_or_app; right; right; left; reflexivity]).
    (* [comment removed for export] *)
    pose proof (grow_n_le3 (lenT + n) ltac:(clear - LTO N0L; subst n; lia)) as GR3. pose proof (w_bounds (grow_n (lenT + n)) ltac:(clear - LTO; subst n; unfold grow_n; Z.div_mod_to_equations; lia)) as WG.
    unfold hideP in *.
    assert (CROOM : croom Lc (wA (grow_n (lenT + n))) (wB (grow_n (lenT + n))) (wBig (grow_n (lenT + n)))).
    { assert (R1 : wA (grow_n (lenT + n)) <= rA) by (clear - SA OWT OWO WG; lia).
      assert (R2 : wB (grow_n (lenT + n)) <= rB) by (clear - SB OWT OWO WG; lia).
      assert (R3 : wBig (grow_n (lenT + n)) <= rBig).
      { clear - SBIG OWT OWO WG GR3 MAXT MAXO LSUM OFF N0 LEN' LTO. subst n.
        remember (owBig KT maxT) as oT eqn:E1. remember (owBig KO maxO) as oO eqn:E2. remember (grow_n (lenT + Z.of_nat n0)) as g eqn:E3. clear E1 E2 E3.
        remember (owA KT maxT) as z1 eqn:E1. remember (owB KT maxT) as z2 eqn:E2. remember (owA KO maxO) as z3 eqn:E3. remember (owB KO maxO) as z4 eqn:E4. clear E1 E2 E3 E4.
        remember (wA g) as y1 eqn:E1. remember (wB g) as y2 eqn:E2. remember (wBig g) as y3 eqn:E3. clear E1 E2 E3.
        remember (Z.of_nat n0) as nz eqn:E4. clear E4.
        assert (A1 : lenT + lenO + len' <= 2 * (e_blen en - e_boff en)) by lia.
        assert (A2 : 3 * y3 <= 4 * lenT + 4 * len' + 24588) by lia.
        assert (A3 : 18 * (e_blen en - e_boff en) + 49158 - 4 * lenT - 4 * lenO <= 3 * rBig) by lia.
        lia. }
      eapply croom_weaken; [exact ROOM| exact R1| exact R2| exact R3]. }
    hide ROLE. hide ELB. hide CG.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply BP with (K := KT) (pl := ql) (BI := tmpv) (meth := methT) (len := lenT) (max := maxT) (LB := LB2) (n := n) (lo := e_lo en) (B := e_B en) (bs := bs);
        [clear - FU REM EVF OFF; lia| exact CROOM| exact CST| rewrite unsigned_lit by lia; rewrite WSP; clear - SLO; lia| exact MBT| clear - LSUM OFF BLEN N0 LEN' LTO; subst n; lia
        | exact OWNL| exact HTL| exact LBS| exact LBC| clear - N0 LEN'; subst n; lia| exact NULn| exact NONULn| reflexivity| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (pd' & max' & -> & HMAX & HFIT & MBT1 & KB & KL & NB & NL & PLS)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    set (KT' := mbk_data KT pd') in MBT1.
    pose proof FRM1 as (CFR1 & KP1 & _). pose proof KP1 as [KB1 KL1].
    destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [NDB0 NDL0]. destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [NDB1 NDL1].
    (* [comment removed for export] *)
    assert (IDS : forall q, In q (mbio_blocks KT ++ mbio_blocks KO ++ [qn; ql]) \/ q = e_pe en \/ In q (mbio_blocks (e_K en)) -> In q (map blk_id LBc)).
    { destruct MBT as [BMX0 MBX0]. destruct MBO as [BMY0 MBY0]. intros q [X|[->|X]].
      - apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBX0 X)|].
        apply in_app_iff in X. destruct X as [X|X]; [exact (mbx_ids _ _ _ _ _ _ _ _ _ _ _ _ MBY0 X)|].
        destruct X as [<-|[<-|[]]]; [exact (cown_id _ _ _ _ _ _ OWNN)| exact (cown_id _ _ _ _ _ _ OWNL)].
      - apply in_map_iff. exists (e_pe en, e_E en, 904). split; [reflexivity| exact INE].
      - apply mbio_T_blocks in X. apply EK in X. apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. exact (PLB _ Hb). }
    unfold hideP in ELB.
    (* [comment removed for export] *)
    assert (CG1 : cgrow Lc L1 (owA KT' max' - owA KT maxT) (owB KT' max' - owB KT maxT) (owBig KT' max' - owBig KT maxT)).
    { destruct PLS as [(EP & -> & -> & ->)|[(q & D & EP & KDN & -> & ->)|(q & D & d & i & nm & EP & KDS & -> & HI & ->)]]; unfold owA, owB, owBig; subst KT'; cbn [k_d mbk_data]; rewrite EP.
      - eapply cgrow_weaken; [apply cgrow_refl| clear; lia| clear; lia| clear; lia].
      - rewrite KDN. eapply cgrow_weaken; [apply cgrow_cons| clear; lia| clear; lia| clear; lia].
      - rewrite KDS. assert (NM : nm = maxT) by (eapply fst_uniq; [exact NDL0| eapply nth_error_In; exact HI| exact (DNT _ KDS)]). subst nm.
        eapply cgrow_weaken; [eapply cgrow_trans; [exact (cgrow_remove _ _ _ _ HI)| apply cgrow_cons]| clear; lia| clear; lia| clear; lia]. }
    assert (COM1 : pem_com libenv en st1 LB1 L1 f1 m1 off (rem - 2) (rA - (owA KT' max' - owA KT maxT)) (rB - (owB KT' max' - owB KT maxT)) (rBig - (owBig KT' max' - owBig KT maxT))).
    { assert (LT1 : 0 <= lenT + n <= max') by (clear - HFIT LTO; subst n; lia). pose proof (ow_bounds KT' max' ltac:(clear - LT1; lia)) as OWT'.
      eapply (com_callI en) with (T1 := mbio_T KT); [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear - REM OFF; lia| exact CG1| | | | | | | exact HT1| exact HK1| exact HE1];
        clear - SA SB SBIG OWT OWO OWT' RA0 RB0 RBIG0 MAXT MAXO GR3 HMAX LSUM OFF N0 LEN' LTO HFIT; subst n; lia. }
    assert (ELB1 : forall b, In b LB1 -> In b (e_LBall en) \/ In (blk_id b) (mbio_blocks KT' ++ mbio_blocks KO ++ [qn; ql])).
    { destruct PLS as [(EP & _ & -> & ->)|[(q & D & EP & KDN & -> & ->)|(q & D & d & i & nm & EP & KDS & -> & HI & ->)]]; subst KT'; unfold mbio_blocks in *; cbn [k_d k_bi k_bb k_bm k_rp mbk_data] in *; rewrite EP.
      - exact ELB.
      - intros b [<-|Hb]; [right; unfold blk_id; cbn [fst]; rewrite !in_app_iff; cbn [In]; tauto|]. rewrite KDN in ELB. destruct (ELB _ Hb) as [X|X]; [left; exact X| right].
        rewrite !in_app_iff in X |- *. cbn [In app] in X |- *. clear - X. tauto.
      - intros b [<-|Hb]; [right; unfold blk_id; cbn [fst]; rewrite !in_app_iff; cbn [In]; tauto|]. apply lb_remove_In in Hb. destruct Hb as [Hb NE].
        rewrite KDS in ELB. destruct (ELB _ Hb) as [X|X]; [left; exact X| right]. rewrite !in_app_iff in X |- *. cbn [In app] in X |- *. clear - X NE. intuition congruence. }
    assert (FRQ : forall q, pd' = Some q -> k_d KT <> Some q -> forall x, In x (map blk_id LBc) -> k_d KT <> Some x -> x <> q).
    { intros q0 EQ NEQ xq X NX E. subst xq. destruct PLS as [(EP & _ & -> & ->)|[(q & D & EP & KDN & -> & ->)|(q & D & d & i & nm & EP & KDS & -> & HI & ->)]].
      - apply NEQ. rewrite <- EP. exact EQ.
      - rewrite EQ in EP. injection EP; intros <-. apply in_map_iff in X. destruct X as ([[q1 A1] n1] & E1 & Hb). cbn in E1. subst q1. exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 Hb eq_refl).
      - rewrite EQ in EP. injection EP; intros <-. apply in_map_iff in X. destruct X as ([[q1 A1] n1] & E1 & Hb). cbn in E1. subst q1.
        eapply (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1); [apply lb_remove_In; split; [exact Hb| unfold blk_id; cbn [fst]; congruence]| reflexivity]. }
    assert (SUBK : forall x, In x (mbio_blocks KT') -> In x (mbio_blocks KT) \/ (pd' = Some x /\ k_d KT <> Some x)).
    { intros xq X. subst KT'. unfold mbio_blocks in *. cbn [k_d k_bi k_bb k_bm k_rp mbk_data] in X. apply in_app_iff in X. destruct X as [X|X]; [left; apply in_or_app; left; exact X|].
      destruct pd' as [q|]; [| destruct X]. destruct X as [<-|[]]. destruct (k_d KT) as [d|] eqn:KD.
      - destruct (decide (d = q)) as [->|NE]; [left; apply in_or_app; right; left; reflexivity| right; split; [reflexivity| congruence]].
      - right. split; [reflexivity| congruence]. }
    assert (KTD : forall x, k_d KT = Some x -> In x (mbio_blocks KT)) by (intros xq E; apply mbio_T_blocks; unfold mbio_T; do 4 right; exact E).
    assert (CFRESH1 : forall b, In b (e_LBall en) -> ~ In (blk_id b) (mbio_blocks KT' ++ mbio_blocks KO ++ [qn; ql])).
    { intros b Hb X. apply in_app_iff in X. destruct X as [X|X]; [| apply (CFRESH _ Hb); apply in_or_app; right; exact X].
      destruct (SUBK _ X) as [Y|[EQ NEQ]]; [apply (CFRESH _ Hb); apply in_or_app; left; exact Y|].
      apply (FRQ _ EQ NEQ (blk_id b)); [apply in_map; exact (PLB _ Hb)| | reflexivity]. intros E. apply (CFRESH _ Hb). apply in_or_app; left. exact (KTD _ E). }
    assert (EL1 : forall q nm, In (q, nm) (e_L en) -> ~ In q (mbio_blocks KT' ++ mbio_blocks KO ++ [qn; ql])).
    { intros q0 nm0 Hq X. apply in_app_iff in X. destruct X as [X|X]; [| apply (EL _ _ Hq); apply in_or_app; right; exact X].
      destruct (SUBK _ X) as [Y|[EQ NEQ]]; [apply (EL _ _ Hq); apply in_or_app; left; exact Y|].
      apply (FRQ _ EQ NEQ q0); [| intros E; apply (EL _ _ Hq); apply in_or_app; left; exact (KTD _ E)| reflexivity].
      destruct CO as (CLB & PERM & IDS0). assert (Z1 : In q0 (map fst Lc)) by (apply in_map_iff; exists (q0, nm0); split; [reflexivity| exact (PLC _ _ Hq)]).
      rewrite <- IDS0 in Z1. apply in_map_iff in Z1. destruct Z1 as (b & E & Hb). rewrite <- E. apply in_map. eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; left; exact Hb]. }
    assert (NDT1 : List.NoDup ((mbio_blocks KT' ++ mbio_blocks KO ++ [qn; ql]) ++ e_pe en :: mbio_blocks (e_K en))).
    { assert (MBK' : mbio_blocks KT' = [k_bi KT; k_bb KT; k_bm KT; k_rp KT] ++ match pd' with Some q => [q] | None => [] end) by (subst KT'; reflexivity).
      assert (MBK : mbio_blocks KT = [k_bi KT; k_bb KT; k_bm KT; k_rp KT] ++ match k_d KT with Some q => [q] | None => [] end) by reflexivity.
      rewrite MBK'. rewrite MBK in IDS, NDT.
      remember (mbio_blocks KO) as BKO eqn:EKO. remember (mbio_blocks (e_K en)) as BKE eqn:EKE. clear EKO EKE.
      destruct PLS as [(EP & _ & _ & _)|[(q & D & EP & KDN & _ & _)|(q & D & d & i & nm & EP & KDS & _ & HI & _)]]; rewrite EP.
      - rewrite <- MBK. exact NDT.
      - rewrite KDN in NDT, IDS. rewrite app_nil_r in NDT, IDS. rewrite <- !app_assoc. rewrite <- !app_assoc in NDT.
        lazymatch goal with |- List.NoDup (?l4 ++ [q] ++ ?rest) => change (List.NoDup (l4 ++ q :: rest)) end.
        apply nd_insert1; [exact NDT|].
        intros X. apply (FRQ q EP ltac:(rewrite KDN; discriminate) q); [| rewrite KDN; discriminate| reflexivity]. apply IDS.
        apply in_app_iff in X. destruct X as [X|X]; [left; apply in_or_app; left; exact X|].
        apply in_app_iff in X. destruct X as [X|X]; [left; apply in_or_app; right; apply in_or_app; left; exact X|].
        apply in_app_iff in X. destruct X as [X|X]; [left; apply in_or_app; right; apply in_or_app; right; exact X|].
        destruct X as [E|X]; [right; left; exact (eq_sym E)| right; right; exact X].
      - rewrite KDS in NDT, IDS. rewrite <- !app_assoc. rewrite <- !app_assoc in NDT.
        lazymatch goal with |- List.NoDup (?l4 ++ [q] ++ ?rest) => change (List.NoDup (l4 ++ q :: rest)); change (List.NoDup (l4 ++ d :: rest)) in NDT end.
        apply nd_insert1; [exact (nd_drop _ _ _ NDT)|].
        intros X. pose proof (nodup_mid_ne _ _ _ _ NDT X) as XD.
        apply (FRQ q EP ltac:(congruence) q); [| congruence| reflexivity]. apply IDS.
        apply in_app_iff in X. destruct X as [X|X]; [left; apply in_or_app; left; apply in_or_app; left; exact X|].
        apply in_app_iff in X. destruct X as [X|X]; [left; apply in_or_app; right; apply in_or_app; left; exact X|].
        apply in_app_iff in X. destruct X as [X|X]; [left; apply in_or_app; right; apply in_or_app; right; exact X|].
        destruct X as [E|X]; [right; left; exact (eq_sym E)| right; right; exact X]. }
    (* [comment removed for export] *)
    assert (DNT1 : forall d', k_d KT' = Some d' -> In (d', max') L1).
    { intros d' E. destruct PLS as [(EP & EM & _ & ->)|[(q & D & EP & KDN & _ & ->)|(q & D & d & i & nm & EP & KDS & _ & HI & ->)]]; subst KT'; cbn [k_d mbk_data] in E.
      - rewrite EM. apply DNT. rewrite <- EP. exact E.
      - rewrite EP in E. injection E; intros <-. left; reflexivity.
      - rewrite EP in E. injection E; intros <-. left; reflexivity. }
    assert (DNO1 : forall d', k_d KO = Some d' -> In (d', maxO) L1).
    { intros d' E. apply KL1; [exact (DNO _ E)|]. apply HTO. unfold mbio_T. do 4 right. exact E. }
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN FRM1 HTN) as OWNN1. pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNL FRM1 HTL) as OWNL1.
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBO FRM1 HTO) as MBO1.
    pose proof (er0_callI en _ _ _ _ _ _ _ _ _ _ ER0 FRM1 INE HE1) as ER1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR1 NMC (proj1 OWNN) HTN ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ql, LB2, 256) CFR1 LBC (proj1 OWNL) HTL ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as LBC1.
    assert (LT1 : 0 <= lenT + n <= max') by (clear - HFIT LTO; subst n; lia). pose proof (ow_bounds KT' max' ltac:(clear - LT1; lia)) as OWT'.
    assert (MAXT1 : 3 * max' <= 4 * (lenT + n) + 12) by (clear - HMAX MAXT GR3 LTO; subst n; lia).
    assert (SA1 : 5 <= rA - (owA KT' max' - owA KT maxT) + owA KT' max' + owA KO maxO) by (clear - SA; lia).
    assert (SB1 : 4 <= rB - (owB KT' max' - owB KT maxT) + owB KT' max' + owB KO maxO) by (clear - SB; lia).
    assert (SBIG1 : 6 * (e_blen en - e_boff en) + 32778 <= rBig - (owBig KT' max' - owBig KT maxT) + owBig KT' max' + owBig KO maxO) by (clear - SBIG; lia).
    assert (REM1 : (Z.to_nat (2 * (e_blen en - off) + 16) <= rem - 2)%nat) by (clear - REM OFF; lia).
    assert (LSUM1 : lenT + n + lenO <= 2 * (off - e_boff en)) by (clear - LSUM N0; subst n; lia).
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    unfold hideP in ROLE.
    (* [comment removed for export] *)
    assert (JG : forall (mX : mem) (endv' : Z) (yra z5 z6 z7 z9 y10 y11 y12 y13 y14 y15 y16 y17 z26 z28 z29 z30 z31 : word),
      (endv' = 0 \/ endv' = 1) -> munch [(bv_unsigned (e_sp en) + -176, bv_unsigned (e_sp en) + -168)]%Z m1 mX -> wmono usegs m1 mX -> mem_inv usegs mX ->
      stk usegs mX (e_lo en) (bv_unsigned (e_sp en) + -208) ->
      rw_cells usegs mX (bv_unsigned (e_sp en) + -208)
        [C8 l0; C8 (wz tmpv); C8 (wz namev); C8 (wz partv); C8 (wz endv'); C8 (wz LB2); C8 (wz (bv_unsigned (e_sp en) + 8)); C8 (wz (bv_unsigned (e_sp en) + 16)); C8 l8; C8 (wz dBv); C8 (wz (e_flags en)); C8 l11; C4 ta; C4 tb] ->
      climpl f1 L1 st1 (MS (mkR yra (wz (bv_unsigned (e_sp en) + -208)) (e_gp en) (e_tp en) z5 z6 z7 (e_sp en) z9 y10 y11 y12 y13 y14 y15 y16 y17
                             (wz len') (wz got) (wz PEM_ENDSTR) (wz (e_flags en)) (wz hBv) (e_sp en) (wz (bv_unsigned (e_sp en) + 24)) (wz (e_BI en)) z26 s11 z28 z29 z30 z31)
                        (e_F en) (wz 0x1883f8) (e_fc en) None mX (seg_rom usegs)) (pem_post libenv errst_live en)).
    { intros mX endv' yra z5 z6 z7 z9 y10 y11 y12 y13 y14 y15 y16 y17 z26 z28 z29 z30 z31 EV' MUx WMx MIx STx LOCx.
      assert (HWx : Forall (wfree LB1 (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ : bptr => True)) [(bv_unsigned (e_sp en) + -176, bv_unsigned (e_sp en) + -168)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
      assert (COMx : pem_com libenv en st1 LB1 L1 f1 mX off (rem - 2) (rA - (owA KT' max' - owA KT maxT)) (rB - (owB KT' max' - owB KT maxT)) (rBig - (owBig KT' max' - owBig KT maxT))).
      { eapply (com_segI en st1 LB1 L1 f1 m1 off (rem - 2)%nat _ _ _ _ mX (fun _ => True)); [exact COM1| exact MUx| exact WMx| exact MIx| exact STx| exact HWx| intros; exact I| unfold e_PL; cbn [disjoint_from fst snd]; clear; lia]. }
      assert (ERx : errst_at_rest (e_E en) [] mX).
      { eapply (er0_segI _ en m1 mX) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact ER1| exact MUx| exact WMx| exact CST1| exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 COM1))))))))| exact HWx| exact I]. }
      assert (MBTx : mbio_rep mX LB1 L1 KT' tmpv methT (lenT + n) max' 0).
      { eapply (mb_seg _ m1 mX) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact MBT1| exact CST1| exact MUx| exact WMx| exact HWx| intros; exact I]. }
      assert (MBOx : mbio_rep mX LB1 L1 KO ov methO lenO maxO 0).
      { eapply (mb_seg _ m1 mX) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact MBO1| exact CST1| exact MUx| exact WMx| exact HWx| intros; exact I]. }
      assert (NMCx : rw_cells usegs mX namev [CB (Z.to_nat nn) (str ++ Z_to_bv 8 0 :: bn2)]) by (eapply rw_cells_transport; [exact NMC1| exact MUx| exact WMx| cbn [disjoint_from cells_size csize fst snd]; clear - RN2 LO SLO NN; lia]).
      assert (LBCx : rw_cells usegs mX LB2 [CB 256 bs]) by (eapply rw_cells_transport; [exact LBC1| exact MUx| exact WMx| cbn [disjoint_from cells_size csize fst snd]; clear - RL2 LO SLO; lia]).
      assert (OUTx : rw_cells usegs mX (bv_unsigned (e_sp en)) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]) by (eapply rw_cells_transport; [exact OUT1| exact MUx| exact WMx| cbn [disjoint_from cells_size csize fst snd]; clear; lia]).
      eapply (G1P en st1 LB1 L1 f1 mX off (rem - 2)%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l0 l8 l11 ta tb qn ql namev nn LB2 hBv dBv tmpv ov got endv' partv str bn2 bs KT' KO methT methO (lenT + n) max' lenO maxO);
        [exact MEAS| exact COMx| | unfold pem_loc, e_PL; exact LOCx| exact EV'| exact PARTV].
      unfold gets_pre. split; [hd_core_by ERx BLEN SA1 SB1 SBIG1 MAXT1 MAXO DNT1 DNO1 GOT ROLE OWNN1 NN LBN NMCx NONUL OWNL1 LBS LBCx MBTx MBOx ELB1 CFRESH1 EL1 NDT1 OUTx| split; [exact REM1| exact LSUM1]]. }
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG LOC OUT NMC LBC MBT MBO.
    pose proof (munch_refl [(bv_unsigned (e_sp en) + -176, bv_unsigned (e_sp en) + -168)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - N0 LEN'; subst n; lia). clear - KZ N0 LEN'. subst n. lia. }
    ths. ths. if_cases KG; zify_cond KG.
    - (* [comment removed for export] *)
      ths. chere. lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mx _) _ =>
        lazymatch goal with MIx : mem_inv usegs mx, STx : stk usegs mx _ _, LOCx : rw_cells usegs mx (bv_unsigned (e_sp en) + -208) _ |- _ =>
          eapply (JG mx 0); [left; reflexivity| exact MU| exact WM| exact MIx| exact STx| exact LOCx] end end.
    - (* [comment removed for export] *)
      ths. ths. if_cases K65; zify_cond K65.
      + (* [comment removed for export] *)
        chere.
        lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mx _) _ => rename mx into m2 end.
        destruct ROLE as [(RG & -> & ->)|(RG & -> & ->)].
        * eapply (FREE2P en st1 LB1 L1 f1 m2 off (rem - 2)%nat _ _ _ [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l0 _ (wz partv) l4 _ _ l8 _ l11 ta tb
                    qn ql namev nn LB2 hBv dBv (str ++ Z_to_bv 8 0 :: bn2) bs KT' KO methT methO (lenT + n) max' lenO maxO);
            [exact COM1| left; split; [reflexivity| exact ER1]| clear - REM OFF; lia| unfold pem_loc; exact LOC1| exact OWNN1| clear - NN; lia| exact LBN| exact NMC1| exact NUL
            | exact OWNL1| exact LBS| exact LBC1| exact MBT1| exact MBO1| intros b Hb; destruct (ELB1 _ Hb) as [X|X]; [left; exact X| right; left; exact X]| intros b []
            | apply Forall_nil| exact CFRESH1| intros b []| exact EL1| exact NDT1| exact OUT1].
        * eapply (FREE2P en st1 LB1 L1 f1 m2 off (rem - 2)%nat _ _ _ [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l0 _ (wz partv) l4 _ _ l8 _ l11 ta tb
                    qn ql namev nn LB2 hBv dBv (str ++ Z_to_bv 8 0 :: bn2) bs KO KT' methO methT lenO maxO (lenT + n) max');
            [exact COM1| left; split; [reflexivity| exact ER1]| clear - REM OFF; lia| unfold pem_loc; exact LOC1| exact OWNN1| clear - NN; lia| exact LBN| exact NMC1| exact NUL
            | exact OWNL1| exact LBS| exact LBC1| exact MBO1| exact MBT1| | intros b []| apply Forall_nil| | intros b []| | | exact OUT1].
          -- intros b Hb. destruct (ELB1 _ Hb) as [X|X]; [left; exact X| right; left]. rewrite !in_app_iff in X |- *. clear - X. tauto.
          -- intros b Hb X. apply (CFRESH1 _ Hb). rewrite !in_app_iff in X |- *. clear - X. tauto.
          -- intros q0 nm0 Hq X. apply (EL1 _ _ Hq). rewrite !in_app_iff in X |- *. clear - X. tauto.
          -- cbn [map app]. eapply Permutation_NoDup; [| exact NDT1]. apply Permutation_app_tail. rewrite (app_assoc (mbio_blocks KT')), (app_assoc (mbio_blocks KO)).
             apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl].
      + (* [comment removed for export] *)
        zstep. zstep. ths. ths. chere. lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mx _) _ =>
          lazymatch goal with MIx : mem_inv usegs mx, STx : stk usegs mx _ _, LOCx : rw_cells usegs mx (bv_unsigned (e_sp en) + -208) _ |- _ =>
            eapply (JG mx); [| exact MU| exact WM| exact MIx| exact STx| exact LOCx] end end.
        clear. lazymatch goal with |- Z.b2z ?c = 0 \/ Z.b2z ?c = 1 => destruct c; cbn; [right| left]; reflexivity end.
  Qed.
End W3.