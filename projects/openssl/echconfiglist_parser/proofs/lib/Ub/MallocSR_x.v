(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac TacX Mem Cells Arr SysStep Exec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Monad MSafeP STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Geom MI_WFree MI_WRelay MI_WRelay2 MmNodes GapGrid KLink KLink2 KLink3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import Malloc_iface MallocBlocks MallocHINV MallocFacts_B MallocFacts_Bpres MallocFacts_inv MallocFacts_inv3 F_malloc_free F_free F_free_K F_free_spec F_malloc_entry.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMallocRep RMallocTree RMallocKit_A RMalloc_iface RMalloc_ifaceP RMalloc_iface_stmt HeapSR_iface MallocSR MallocSR_hyps.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RF_malloc_top RF_malloc_spec RF_free_spec F_memcpy RF_realloc_A RF_realloc_B RF_realloc_C RF_aalloc_A RF_aalloc_B RF_aalloc_C RF_realloc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import SReach SReachTree SReachCjNodes.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaRel.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require MI_Cnt.   (* [comment removed for export] *)
Local Ltac lia ::=
  dle_wrap ltac:(first [ n8v_prune1p; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | n8v_prune1; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | n8v_prunep; Zify.zify; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Theorem rauxv_elim_proof : HeapSR_iface.rauxv_elim HS.
Proof.
  unfold HeapSR_iface.rauxv_elim. cbn [HeapSR_iface.hs_rauxv_ok HS].
  intros m B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C & A1 & A2 & H).
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd, hsecret.
  split; [exact C|]. split; [exact A1|]. split; [exact A2|].
  pose proof hsecret_range. repeat (split; [tauto|]). lia.
Qed.

Theorem statics_of_RHEAP_proof : HeapSR_iface.statics_of_RHEAP HS.
Proof.
  unfold HeapSR_iface.statics_of_RHEAP. cbn [HeapSR_iface.hs_RHEAP HS].
  intros s LB m (st & LB0 & _ & _ & MR & _).
  destruct MR as (_ & _ & (G1 & G2 & G3 & G4 & G5 & G6) & _).
  split; [exact G2|]. split; [exact G4|]. split; [apply hcanary_range| exact G5].
Qed.

Theorem RHEAP_perm_law_proof : HeapSR_iface.RHEAP_perm_law HS.
Proof. unfold HeapSR_iface.RHEAP_perm_law. cbn [HeapSR_iface.hs_RHEAP HS]. intros s LB LB' m H P. exact (RHEAP_perm s LB LB' m H P). Qed.

Theorem RHEAP_slack_law_proof : HeapSR_iface.RHEAP_slack_law HS.
Proof. try hcb. try hsb.
  unfold HeapSR_iface.RHEAP_slack_law. cbn [HeapSR_iface.hs_RHEAP HS]. intros s LB m p A n HR HIN.
  destruct HR as (st & LB0 & PERM & Hst & RM & [BLK AR] & RZ).
  assert (HIN0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact HIN]).
  destruct (areach_inv _ _ _ AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR HIN0) as (k & Hk & (C1 & C2 & C3)). destruct k as [[c off] nn]. cbn [MallocBlocks.blk_slot MallocBlocks.blk_size MallocBlocks.blk_addr bslot bsize boff fst snd] in C1, C2, C3. subst nn.
  destruct (MI_WFree.block_facts x0 st L BL LS INV c off n Hk) as (mm & bm & i & ai & aa & ar & ka & BF).
  destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r & Hr & Kr).
  assert (HA : A = bk_P c off r).
  { rewrite C3. unfold bk_P. rewrite (conc_region' st c r) by (rewrite (bk_c st c off n mm bm i ai aa ar ka BF); exact Hr). reflexivity. }
  rewrite HA. exact (bk_slack_wr st L BL LS c off n mm bm i ai aa ar ka r INV BF Hr m RM (proj1 RM)).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_CB2 : forall m A bs1 bs2 n1 n2,
  length bs1 = n1 -> length bs2 = n2 ->
  bytes_at usegs m A (bs1 ++ bs2) -> wr_at usegs m A (Z.of_nat (n1 + n2)) -> rw_cells usegs m A [CB n1 bs1; CB n2 bs2].
Proof. try hcb. try hsb.
  intros m A bs1 bs2 n1 n2 L1 L2 B W. apply rw_cells_of_bytes; cbn; [auto| rewrite app_nil_r; exact B| rewrite Nat.add_0_r; exact W].
Qed.

Section Realloc.
Hypothesis P2 : PHASE2.

(* [comment removed for export] *)
Lemma realloc_inplace_sr :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (p : bptr) (A n n' lo B : Z)
         (pre : list byte) (errv : word) (mo : Model)
         (st : mstate) (LB0 : list block) (L : mled) (BL : list blk) (LS : lhead -> list aptr)
         (c : cptr) (off : Z) (mm bm : aptr) (i ai : Z) (aa : aptr) (ar : area) (ka : Z) (r : region),
    Permutation LB0 LB -> strip st = ps_m s -> rmrep st m -> brk_link st (ps_brk s) -> AREACH_from ref_reserved st LB0 -> rstatic_zero m ->
    INVL x0 st L BL LS -> CORR st LB0 BL -> In ((c, off), n) BL -> blk_facts st c off n mm bm i ai aa ar ka ->
    s_regions st !! (fst bm) = Some r -> gmeta_ok st mm bm -> ticks_ok st -> 0 <= c_secret (ctx st) < 2 ^ 64 ->
    List.NoDup (map blk_slot LB0) ->
    blk_slot (p, A, n) = c -> A = bk_P c off r ->
    KM s mo -> In (p, A, n) LB ->
    bytes_at usegs m A pre -> Z.of_nat (length pre) = n ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - HeapSR_iface.RREALLOC_STACK ->
    rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n' -> 1 <= n' < HeapSR_iface.RMMAP_THRESHOLD ->
    rinplace n' (bk_E st c mm r - bk_P c off r) (bk_sc st mm) = true ->
    sreach usegs (HeapSR_iface.realloc_sr_post HS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n n' lo B pre m mo)
       (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x2b7cd0) fc None m (seg_rom usegs)) mo).
Proof. try hcb. try hsb.
  intros until r. intros PERM Hst RM BLK AR RZ INV CR Hk BF Hr GO TK SECR ND0 SLOT HA KMs HIN BY LEN AUX HB ST CLO LO ERR MI TP A0 A1 N IP.
  pose proof KMs as (Lk & CRk & Kk & Bk).
  unfold HeapSR_iface.RREALLOC_STACK, RMALLOC_STACK in LO. unfold HeapSR_iface.RMMAP_THRESHOLD in N.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof AUX as (av0 & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & AVB). 
  assert (SPH : bv_unsigned sp + 8 <= 2 ^ 64) by (clear -AVB HB; lia). clear AVB av0 x3 x4 x5 x16 x6 x11 x12 x23 rnd.
  eapply sreach_mono.
  { eapply (cj_evt_sreach usegs _ _ mo (kb_halt _ _ _ Kk) (proj1 (kb_minv _ _ _ Kk))).
    eapply (rre_inplace_evt st L BL LS c off n mm bm i ai aa ar ka r INV BF Hr GO); try eassumption.
    - clear -LO. lia.
    - rewrite A0, HA. reflexivity. }
  cbv beta. intros cf [POST EMO].
  destruct POST as (m1 & u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & Ems & MI2 & MU & WM & MI1 & RM1 & ST1 & FR1).
  (* [comment removed for export] *)
  pose proof RM as (WF & _).
  destruct (bk_all st L BL LS c off n mm bm i ai aa ar ka r INV Hk BF Hr WF)
    as ((B0 & BAL & S0 & S16 & SPAN & BC) & (Hi & Hoff & Hn & Hfit & R0 & RS & B3) & [SK SKL] & SC & [ST16 STM] & G63 & SST & DRr & _).
  unfold UNIT, IB in Hfit, RS, SC.
  unfold rinplace in IP. apply andb_true_iff in IP as [IP1 IP2]. apply Z.leb_le in IP1. apply Z.leb_le in IP2.
  pose proof (size_to_class_props n' ltac:(unfold MMAP_THRESHOLD; clear -N; lia)) as (SCR & _ & _).
  assert (SC48 : bk_sc st mm < 48) by (destruct (Z.lt_ge_cases (bk_sc st mm) 48) as [LT|GE]; [exact LT| pose proof (G63 GE); clear -H SCR IP2; lia]).
  pose proof (SST SC48) as SST'.
  set (P := bk_P c off r) in *. set (E := bk_E st c mm r) in *. set (stride := bk_stride st mm) in *.
  assert (EP : P = r_base r + snd c + 16 * off) by reflexivity.
  assert (EE : E = r_base r + snd c + stride - 4) by reflexivity.
  assert (FIT' : UNIT * off + n' <= stride - IB) by (unfold UNIT, IB; clear -IP1 EP EE; lia).
  assert (GEO : 16 <= P /\ P + n <= E /\ P + n' <= E /\ E + 4 <= hceil /\ hceil + 8256 <= bv_unsigned sp)
    by (rewrite EP, EE; clear -B0 S0 SC SK SKL SPAN BC Hoff Hfit Hn IP1 CLO LO ST16 EP EE; lia).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (CLS' : 27 <= bk_sc st mm -> 2028 < n').
  { intros H27. destruct (Z.le_gt_cases n' 2716) as [LE|GT]; [| clear -GT; lia].
    pose proof (MI_Cnt.size_to_class_small n' ltac:(clear -N LE; lia)) as S25. clear -H27 IP2 S25. lia. }
  destruct (rre_inplace_rep st L BL LS c off n mm bm i ai aa ar ka r INV BF Hr m1 n' RM1 TK ltac:(clear -GEO N; lia) FIT' SC48 CLS') as (RM2 & TK2 & ROK & STRIP & CONC & REG & CTX).
  set (W := ss_list c off n' stride i) in *. set (st' := relay st W c off n') in *.
  set (m2 := rre_ss_mem m1 P E n' (bk_b3 st c off n mm i r)) in *.
  (* [comment removed for export] *)
  set (C := fun a => (bv_unsigned sp - 64 <= a < bv_unsigned sp) \/ a = P - 3 \/ P + n' <= a < E).
  assert (PE : rpres_except C m m2).
  { subst m2. apply rpres_rre_ss; [| clear -GEO EP B0 S0 SC SK Hoff; lia| clear -GEO N; lia| clear -GEO IP1; lia| clear -GEO EE BC SPAN SC SKL HCEILB; lia| clear -GEO N EE EP SST' Hoff; lia| subst C; cbv beta; clear; tauto| subst C; cbv beta; clear; intros; tauto].
    eapply rpres_except_of_munch; [exact MU| exact WM|]. subst C. cbv beta. intros a Ha NC. cbn. clear -GEO NC. lia. }
  assert (NCimg : forall a, 0x2c5000 <= a < 0x358000 -> ~ C a).
  { intros a Ha. subst C. cbv beta. clear -GEO Ha CLO LO DRr EP EE B0 S0 SC SK SKL SPAN HCEILB Hfit Hoff Hn ST16 N. intros [X|[X|X]]; lia. }
  assert (NChi : forall a, bv_unsigned sp <= a -> ~ C a).
  { intros a Ha. subst C. cbv beta. clear -GEO Ha CLO LO EP EE BC SPAN SC SKL Hoff Hfit ST16 SK N Hn. intros [X|[X|X]]; lia. }
  (* [comment removed for export] *)
  assert (HR0 : RHEAP s LB m) by (exists st, LB0; split; [exact PERM|]; split; [exact Hst|]; split; [exact RM|]; split; [split; [exact BLK| exact AR]| exact RZ]).
  assert (LBRM : lb_remove p LB = lbrm LB (p, A, n)).
  { apply (lb_remove_lbrm LB p A n); [| exact HIN]. eapply NoDup_map_perm; [exact PERM| exact ND0]. }
  assert (NCblk : forall b a, In b (lb_remove p LB) -> blk_addr b <= a < blk_addr b + blk_size b -> ~ C a).
  { intros b a Hb Hab. rewrite LBRM in Hb. unfold lbrm in Hb. apply In_filter_iff in Hb. destruct Hb as [Hb NEb]. rewrite SLOT in NEb.
    assert (Hb0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
    destruct (Forall2_In_l _ _ _ _ CR Hb0) as (k & Hk' & (C1 & C2 & C3)).
    assert (NEk : bslot k <> c) by (rewrite <- C1; intros E0; rewrite E0, aptr_eqb_refl in NEb; exact NEb).
    pose proof (RHEAP_block_range_proof s LB m b HR0 Hb) as (RB1 & _ & RB3 & RB4 & _).
    destruct (bk_blk_sep st L BL LS c off n mm bm i ai aa ar ka r INV BF Hr WF k Hk' NEk) as [D|D];
      rewrite <- C3 in D; rewrite <- ?C2 in D; subst C; cbv beta; unfold RMalloc_iface_stmt.blk_addr, RMalloc_iface_stmt.blk_size in Hab;
      unfold MallocBlocks.blk_addr, MallocBlocks.blk_size in D, RB4; clear -GEO D Hab RB4 CLO LO EP EE Hoff N SC Hfit Hn; intros [X|[X|X]]; lia. }
  assert (HP : rheap_pres (lb_remove p LB) (bv_unsigned sp) m m2).
  { intros a Ha Hc. apply PE; [exact Ha|]. destruct Hc as [X|[[X1 X2]|(b & Hb & Hab)]]; [apply NChi; exact X| apply NCimg; exact X1| eapply NCblk; [exact Hb| exact Hab]]. }
  (* [comment removed for export] *)
  assert (ETP : errno_addr tp = RMalloc_iface_stmt.RERRNO) by (rewrite TP; unfold errno_addr, RMalloc_iface_stmt.RATP, RMallocRep.RATP, RMalloc_iface_stmt.RERRNO; rewrite unsigned_lit by (clear; lia); reflexivity).
  rewrite ETP in ERR.
  assert (ERR2 : rw_cells usegs m2 RERRNO [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE| exact ERR|]. cbn. intros a Ha. apply NCimg. unfold RMallocRep.RERRNO, RMalloc_iface_stmt.RERRNO, RMallocRep.RATP, RMalloc_iface_stmt.RATP in Ha. clear -GEO Ha. lia. }
  assert (AUX2 : rauxv_ok m2 B).
  { eapply rauxv_ok_pres_B; [exact AUX| exact PE| intros a Ha; apply NChi; clear -GEO Ha HB; lia| intros a Ha; apply NCimg; unfold RMallocRep.RAUXV_CELL, RMalloc_iface_stmt.RAUXV_CELL in Ha; clear -GEO Ha; lia]. }
  assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { subst m2. eapply rpres_except_rw_cells.
    - apply (rpres_rre_ss (fun a => a = P - 3 \/ P + n' <= a < E) m1 m1); [apply rpres_except_refl| clear -GEO EP B0 S0 SC SK Hoff; lia| clear -GEO N; lia| clear -GEO IP1; lia
        | clear -GEO EE BC SPAN SC SKL HCEILB; lia| clear -GEO N EE EP SST' Hoff; lia| clear; tauto| clear; intros; tauto].
    - exact FR1.
    - cbn. intros a Ha. clear -GEO Ha CLO LO EP EE BC SPAN SC SKL Hoff SK N. intros [X|X]; lia. }
  assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -64)).
  { subst m2. eapply rpres_except_stk.
    - apply (rpres_rre_ss (fun a => a = P - 3 \/ P + n' <= a < E) m1 m1); [apply rpres_except_refl| clear -GEO EP B0 S0 SC SK Hoff; lia| clear -GEO N; lia| clear -GEO IP1; lia
        | clear -GEO EE BC SPAN SC SKL HCEILB; lia| clear -GEO N EE EP SST' Hoff; lia| clear; tauto| clear; intros; tauto].
    - exact ST1.
    - intros a Ha. clear -GEO Ha CLO LO EP EE BC SPAN SC SKL Hoff SK N. intros [X|X]; lia. }
  release_frame FR2 ST2 (bv_unsigned sp).
  (* [comment removed for export] *)
  set (mn := Z.min n n').
  assert (MN : 0 <= mn <= n /\ mn <= n') by (subst mn; clear -GEO Hn N; lia).
  assert (WR2 : wr_at usegs m2 P n').
  { pose proof RM2 as (_ & _ & _ & _ & _ & SH2). destruct (SH2 (fst bm) r ltac:(rewrite REG; exact Hr) ltac:(exact (bk_Kr st L BL LS c off n mm bm i ai aa ar ka r INV BF Hr))) as [HW _].
    eapply wr_at_sub; [exact HW| clear -GEO EP S0 SC SK Hoff; lia| clear -GEO IP1 EP EE SPAN SC SKL; lia]. }
  assert (BY2 : bytes_at usegs m2 P (firstn (Z.to_nat mn) pre)).
  { eapply rpres_except_bytes_at; [exact PE| |].
    - rewrite <- HA. destruct BY as (Y0 & Y1 & YB). split; [exact Y0|]. split; [rewrite firstn_length_le by (clear -GEO MN LEN; lia); clear -GEO Y1 MN LEN; lia|].
      intros j Hj. rewrite firstn_length_le in Hj by (clear -GEO MN LEN; lia). rewrite (YB j) by (clear -GEO Hj MN LEN; lia).
      rewrite nth_error_firstn. replace (PeanoNat.Nat.ltb j (Z.to_nat mn)) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; exact Hj). reflexivity.
    - rewrite firstn_length_le by (clear -GEO MN LEN; lia). intros a Ha. subst C. cbv beta. clear -GEO Ha MN CLO LO EP EE BC SPAN SC SKL Hoff. intros [X|[X|X]]; lia. }
  destruct (rwr_at_bytes_exist m2 (P + mn) (n' - mn) ltac:(eapply wr_at_sub; [exact WR2| clear -GEO MN; lia| clear -GEO MN; lia]) ltac:(clear -GEO MN; lia)
              ltac:(clear -GEO DRr EP EE SC SK SKL SPAN Hoff MN IP1 S0; lia)) as (junk & JL & JB).
  assert (CH : rw_cells usegs m2 P [CB (Z.to_nat mn) (firstn (Z.to_nat mn) pre); CB (Z.to_nat (n' - mn)) junk]).
  { apply rw_cells_CB2; [rewrite firstn_length_le by (clear -GEO MN LEN; lia); reflexivity| exact JL| |].
    - apply bytes_at_app. split; [exact BY2|]. rewrite firstn_length_le by (clear -GEO MN LEN; lia). rewrite Z2Nat.id by (clear -GEO MN; lia). exact JB.
    - replace (Z.of_nat (Z.to_nat mn + Z.to_nat (n' - mn))) with n' by (clear -GEO MN; lia). exact WR2. }
  (* [comment removed for export] *)
  unfold HeapSR_iface.realloc_sr_post.
  cbn [HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_lb_remove HS].
  exists u0, u1, u2, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m2, errv, A, junk, (c, off), s.
  split; [rewrite Ems, A0; reflexivity|].
  split; [rewrite EMO; exact KMs|]. split; [rewrite EMO; apply vm_only_refl|].
  split; [exact MI2|]. split; [exact ST2|]. split; [change (bv_unsigned tp + -164) with (errno_addr tp); rewrite ETP; exact ERR2|]. split; [exact AUX2|]. split; [exact HP|].
  split. { rewrite HA. split; [clear -GEO EP B0 S0 SC SK Hoff; lia|]. split; [| split; [clear -GEO N; lia| split; [clear -GEO IP1 EP EE BC SPAN SC SKL; lia| clear -GEO DRr EP EE SC SK SKL SPAN Hoff IP1 S0 Hfit Hn; lia]]].
           rewrite EP, SC. pose proof (Z.div_mod stride 16 ltac:(clear; lia)) as D1. rewrite STM in D1. pose proof (Z.div_mod (snd bm) 16 ltac:(clear; lia)) as D2. rewrite S16 in D2.
           pose proof (Z.div_mod (r_base r) 4096 ltac:(clear; lia)) as D3. rewrite BAL in D3.
           replace (r_base r + (snd bm + 16 + stride * i) + 16 * off) with ((r_base r / 4096 * 256 + snd bm / 16 + 1 + stride / 16 * i + off) * 16) by (clear -GEO D1 D2 D3; lia).
           apply Z_mod_mult. }
  split; [| rewrite HA; exact CH].
  (* [comment removed for export] *)
  exists st', (((c, off), conc st c + UNIT * off, n') :: lbrm LB0 (p, A, n)).
  split. { rewrite LBRM. replace (conc st c + UNIT * off) with A. 2:{ rewrite HA, EP, (conc_region' st c r) by (rewrite (bk_c st c off n mm bm i ai aa ar ka BF); exact Hr). unfold UNIT. clear; lia. }
           apply perm_skip. apply lbrm_perm. exact PERM. }
  split; [rewrite STRIP; exact Hst|]. split; [exact RM2|]. split; [split|].
  3:{ unfold rstatic_zero in *. eapply rpres_except_rw_cells; [exact PE| exact RZ|]. cbn. intros a Ha. apply NCimg. unfold RMalloc_iface_stmt.RCTX, RMallocRep.RCTX in Ha. clear -Ha. lia. }
  - unfold brk_link in BLK |- *. rewrite CTX. destruct (Malloc.c_brk (Malloc.ctx st)); try exact BLK. rewrite CONC. exact BLK.
  - subst st' W. rewrite <- SLOT. unfold lbrm. apply (areach_relay st LB0 (p, A, n) _ off n' AR).
    + eapply Permutation_in; [apply Permutation_sym; exact PERM| exact HIN].
    + rewrite SLOT. exact ROK.
Qed.

(* [comment removed for export] *)
Lemma realloc_move_sr :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (p : bptr) (A n n' lo B : Z)
         (pre : list byte) (errv : word) (mo : Model)
         (st : mstate) (LB0 : list block) (L : mled) (BL : list blk) (LS : lhead -> list aptr)
         (c : cptr) (off : Z) (mm bm : aptr) (i ai : Z) (aa : aptr) (ar : area) (ka : Z) (r : region),
    Permutation LB0 LB -> strip st = ps_m s -> rmrep st m -> brk_link st (ps_brk s) -> AREACH_from ref_reserved st LB0 -> rstatic_zero m ->
    INVL x0 st L BL LS -> CORR st LB0 BL -> In ((c, off), n) BL -> blk_facts st c off n mm bm i ai aa ar ka ->
    s_regions st !! (fst bm) = Some r -> gmeta_ok st mm bm -> ticks_ok st -> 0 <= c_secret (ctx st) < 2 ^ 64 ->
    List.NoDup (map blk_slot LB0) ->
    blk_slot (p, A, n) = c -> A = bk_P c off r ->
    KM s mo -> In (p, A, n) LB -> alloc_ok s LB n' ->
    bytes_at usegs m A pre -> Z.of_nat (length pre) = n ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - HeapSR_iface.RREALLOC_STACK ->
    rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n' -> 1 <= n' < HeapSR_iface.RMMAP_THRESHOLD ->
    rinplace n' (bk_E st c mm r - bk_P c off r) (bk_sc st mm) = false ->
    sreach usegs (HeapSR_iface.realloc_sr_post HS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n n' lo B pre m mo)
       (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x2b7cd0) fc None m (seg_rom usegs)) mo).
Proof. try hcb. try hsb.
  intros until r. intros PERM Hst RM BLK AR RZ INV CR Hk BF Hr GO TK SECR ND0 SLOT HA KMs HIN AOK BY LEN AUX HB ST CLO LO ERR MI TP A0 A1 N IP.
  pose proof KMs as (Lk & CRk & Kk & Bk).
  unfold HeapSR_iface.RREALLOC_STACK, RMALLOC_STACK in LO. unfold HeapSR_iface.RMMAP_THRESHOLD in N.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof AUX as (av0 & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & AVB).
  assert (SPH : bv_unsigned sp + 8 <= 2 ^ 64) by (clear -AVB HB; lia). clear AVB av0 x3 x4 x5 x16 x6 x11 x12 x23 rnd.
  pose proof RM as (WF & _).
  destruct (bk_all st L BL LS c off n mm bm i ai aa ar ka r INV Hk BF Hr WF)
    as ((B0 & BAL & S0 & S16 & SPAN & BC) & (Hi & Hoff & Hn & Hfit & R0 & RS & B3) & [SK SKL] & SC & [ST16 STM] & G63 & SST & DRr & _).
  unfold UNIT, IB in Hfit, RS, SC.
  set (P := bk_P c off r) in *. set (E := bk_E st c mm r) in *. set (stride := bk_stride st mm) in *.
  assert (EP : P = r_base r + snd c + 16 * off) by reflexivity.
  assert (EE : E = r_base r + snd c + stride - 4) by reflexivity.
  assert (GEO : 16 <= P /\ P + n <= E /\ E + 4 <= hceil /\ hceil + 8256 <= bv_unsigned sp)
    by (rewrite EP, EE; clear -B0 S0 SC SK SKL SPAN BC Hoff Hfit Hn CLO LO ST16 EP EE; lia).
  assert (ERES : bk_res st c off n mm r = E - P - n) by reflexivity.
  assert (ETP : errno_addr tp = RMalloc_iface_stmt.RERRNO) by (rewrite TP; unfold errno_addr, RMalloc_iface_stmt.RATP, RMallocRep.RATP, RMalloc_iface_stmt.RERRNO; rewrite unsigned_lit by (clear; lia); reflexivity).
  (* [comment removed for export] *)
  set (Q0 := fun ms => exists (m1 : mem) (t1' t2' a2' a4' a5' a7' t4' : word),
                 ms = MS (mkR (Z_to_bv 64 0x2b8068) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) t1' t2' (Z_to_bv 64 n') a0 (Z_to_bv 64 n') (Z_to_bv 64 n') a2' (Z_to_bv 64 (bk_sc st mm)) a4' a5'
                                         (Z_to_bv 64 (E + 4)) a7' (Z_to_bv 64 (E - (E - P - n))) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4' t5 t6)
                                 F (Z_to_bv 64 rmalloc_entry) fc None m1 (seg_rom usegs)
                 /\ rw_cells usegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                 /\ stk usegs m1 lo (bv_unsigned sp + -64) /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ rmrep st m1).
  eapply sreach_seq.
  { eapply (cj_evt_sreach usegs Q0 _ mo (kb_halt _ _ _ Kk) (proj1 (kb_minv _ _ _ Kk))).
    eapply evt_cut; [eapply (rre_front st L BL LS c off n mm bm i ai aa ar ka r INV BF Hr GO SECR); try eassumption; [clear -GEO LO; lia| rewrite A0, HA; reflexivity]|].
    intros ms1 (m1 & t4' & D & FR1 & ST1 & MU1 & WM1 & MI1 & RM1).
    destruct D as (a2' & a4' & a5' & a7' & t1' & t2' & ->). fold P E in IP. rewrite ERES, IP.
    eapply evt_mono; [eapply (rre_mv1_walk _ _ gp tp _ t1' t2' s0 (wz (conc st mm)) a0 _ a2' (Z_to_bv 64 (bk_sc st mm)) a4' a5' _ a7' _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ t4' t5 t6 F fc m1 n' eq_refl ltac:(clear -N; lia))|].
    intros ms2 ->. subst Q0. cbv beta. exists m1, t1', t2', a2', a4', a5', a7', t4'. auto 10. }
  subst Q0. cbv beta. intros c1 [(m1 & t1' & t2' & a2' & a4' & a5' & a7' & t4' & E1 & FR1 & ST1 & MU1 & WM1 & MI1 & RM1) EMO1].
  destruct c1 as [ms1 mo1]. cbn in E1, EMO1. subst ms1 mo1.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear -GEO SPR HCEILB; lia).
  assert (RZ1 : rstatic_zero m1).
  { unfold rstatic_zero in *. eapply rw_cells_transport; [exact RZ| exact MU1| exact WM1|]. cbn. unfold RMalloc_iface_stmt.RCTX, RMallocRep.RCTX. clear -GEO HCEILB. lia. }
  assert (HR1 : RHEAP s LB m1) by (exists st, LB0; split; [exact PERM|]; split; [exact Hst|]; split; [exact RM1|]; split; [split; [exact BLK| exact AR]| exact RZ1]).
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. constructor; [| constructor]. cbn. unfold RMallocRep.RAUXV_CELL. clear -HB GEO HCEILB. lia. }
  rewrite ETP in ERR.
  assert (ERR1 : rw_cells usegs m1 RMalloc_iface_stmt.RERRNO [C4 errv]).
  { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold RMalloc_iface_stmt.RERRNO. clear -GEO HCEILB. lia. }
  (* [comment removed for export] *)
  pose proof (malloc_sr_at P2 rmalloc_entry RMALLOC_STACK rmalloc_body) as MSR.
  unfold HeapSR_iface.malloc_sr_stmt_at in MSR. cbn [HeapSR_iface.hs_SR HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_alloc_ok HS] in MSR.
  eapply sreach_seq.
  { eapply (MSR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB n' lo B errv mo HR1 KMs AOK AUX1);
      rewrite ?USP; [clear -HB; lia| exact ST1| exact CLO| unfold RMALLOC_STACK; clear -LO; lia| rewrite ETP; exact ERR1| exact MI1| exact TP| reflexivity| clear -N; lia]. }
  clear MSR. cbv beta. intros c2 POST2.
  destruct POST2 as (v0 & v1 & v2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & v3 & v4 & v5 & v6 & m2 & errv2 & A' & junk & p' & s' & E2 & KM2 & VO2 & MI2 & ST2 & ERR2 & AUX2 & PRES2 & RNG2 & HR2 & CH2).
  destruct c2 as [ms2 mo2]. cbn in E2, KM2, VO2. subst ms2. rewrite USP in ST2, PRES2.
  replace (ret_pc (Z_to_bv 64 2850920)) with (Z_to_bv 64 2850920) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  pose proof RNG2 as (RA1 & RA2 & RA3 & RA4 & RA5).
  set (mn := Z.min n' n).
  assert (MN : 0 <= mn <= n /\ mn <= n') by (subst mn; clear -Hn N; lia).
  (* [comment removed for export] *)
  assert (BY1 : bytes_at usegs m1 P (firstn (Z.to_nat mn) pre)).
  { eapply bytes_at_transport; [| exact MU1|].
    - rewrite <- HA. destruct BY as (Y0 & Y1 & YB). split; [exact Y0|]. split; [rewrite firstn_length_le by (clear -MN LEN; lia); clear -Y1 MN LEN; lia|].
      intros j Hj. rewrite firstn_length_le in Hj by (clear -MN LEN; lia). rewrite (YB j) by (clear -Hj MN LEN; lia).
      rewrite nth_error_firstn. replace (PeanoNat.Nat.ltb j (Z.to_nat mn)) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; exact Hj). reflexivity.
    - rewrite firstn_length_le by (clear -MN LEN; lia). cbn. clear -GEO MN. lia. }
  assert (BY2 : bytes_at usegs m2 P (firstn (Z.to_nat mn) pre)).
  { eapply rheap_pres_bytes_at; [exact PRES2| exact BY1|]. rewrite firstn_length_le by (clear -MN LEN; lia).
    right. right. exists (p, A, n). split; [exact HIN|]. cbn. rewrite HA. fold P. clear -MN. lia. }
  (* [comment removed for export] *)
  assert (SEP : P + mn <= A' \/ A' + mn <= P).
  { destruct (fresh_block_disjoint_client _ RHEAP_block_range_proof RHEAP_blocks_disjoint_proof RHEAP_blocks_nodup_proof s' LB m2 p' A' n' (bv_unsigned sp) P mn HR2
               ltac:(right; right; exists (p, A, n); split; [exact HIN|]; cbn; rewrite HA; fold P; clear -MN; lia) ltac:(clear -GEO; lia) ltac:(clear -MN; lia)); clear -H MN; lia. }
  destruct CH2 as [[CWF CBY] CWR]. cbn [cells_bytes cbytes cells_size csize app] in CWF, CBY, CWR. rewrite app_nil_r in CBY. rewrite Nat.add_0_r in CWR. destruct CWF as [JL _].
  assert (CHd : rw_cells usegs m2 A' [CB (Z.to_nat mn) (firstn (Z.to_nat mn) junk)]).
  { apply rw_cells_of_bytes; cbn.
    - split; [| exact I]. rewrite firstn_length_le by (rewrite JL; clear -MN; lia). reflexivity.
    - rewrite app_nil_r. destruct CBY as (Y0 & Y1 & YB). split; [exact Y0|]. split; [rewrite firstn_length_le by (rewrite JL; clear -MN; lia); rewrite JL in Y1; clear -Y1 MN; lia|].
      intros j Hj. rewrite firstn_length_le in Hj by (rewrite JL; clear -MN; lia). rewrite (YB j) by (rewrite JL; clear -Hj MN; lia).
      rewrite nth_error_firstn. replace (PeanoNat.Nat.ltb j (Z.to_nat mn)) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; exact Hj). reflexivity.
    - rewrite Nat.add_0_r. eapply wr_at_sub; [exact CWR| clear; lia| clear -MN; lia]. }
  (* [comment removed for export] *)
  set (Q2 := fun ms => exists (m3 : mem) (q0 q1 q2 z1 z2 z3 z4 z5 z6 z7 q3 q4 q5 q6 : word),
           ms = MS (mkR (Z_to_bv 64 0x2b8088) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp q0 q1 q2 (Z_to_bv 64 A') a0 (Z_to_bv 64 A') z1 z2 z3 z4 z5 z6 z7
                            (Z_to_bv 64 (E - (E - P - n))) s3 s4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6) F (ret_pc (Z_to_bv 64 0x2b8088)) fc None m3 (seg_rom usegs)
           /\ munch [(A', A' + mn)]%Z m2 m3 /\ wmono usegs m2 m3 /\ mem_inv usegs m3
           /\ rw_cells usegs m3 A' [CB (Z.to_nat mn) (firstn (Z.to_nat mn) pre)]).
  eapply sreach_seq.
  { eapply (cj_evt_sreach usegs Q2 _ mo2 (proj1 (KM_halted_lazy _ _ KM2)) (proj2 (KM_halted_lazy _ _ KM2))).
    eapply evt_cut.
    { eapply (rre_mv2_walk _ _ gp tp v0 v1 v2 a0 _ y1 y2 y3 y4 y5 y6 y7 _ s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F fc m2 n' P A' n (E - (E - P - n)));
        [reflexivity| clear -RA1 RA3 RA4 HCEILB; lia| rewrite A0, HA; apply unsigned_lit; clear -GEO HCEILB Hn; lia| reflexivity| clear; lia| exact Hn| clear -GEO HCEILB Hn; lia| clear -N; lia]. }
    intros ms3 ->.
    eapply evt_mono.
    { eapply (memcpy_spec _ _ gp tp v0 v1 v2 (Z_to_bv 64 A') a0 (Z_to_bv 64 A') a0 (Z_to_bv 64 (Z.min n' n)) y3 y4 y5 y6 y7 _ s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F fc m2 (firstn (Z.to_nat mn) pre) (firstn (Z.to_nat mn) junk)).
      - rewrite A0, HA, unsigned_lit by (clear -GEO HCEILB Hn; lia). exact BY2.
      - rewrite firstn_length_le by (clear -MN LEN; lia). rewrite unsigned_lit by (clear -N Hn; lia). reflexivity.
      - rewrite !unsigned_lit by (clear -MN RA1 RA3 RA4 HCEILB Hn N; lia). fold mn. exact CHd.
      - rewrite A0, HA, !unsigned_lit by (clear -MN RA1 RA3 RA4 GEO HCEILB Hn N; lia). fold mn. clear -SEP. lia.
      - exact MI2. }
    intros ms4 PM. unfold memcpy_post in PM. destruct PM as (q0 & q1 & q2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & q3 & q4 & q5 & q6 & m3 & -> & MU3 & WM3 & MI3 & CH3 & _).
    rewrite !unsigned_lit in MU3 by (clear -MN RA1 RA3 RA4 GEO HCEILB Hn N; lia). rewrite !unsigned_lit in CH3 by (clear -MN RA1 RA3 RA4 GEO HCEILB Hn N; lia). fold mn in MU3. fold mn in CH3.
    subst Q2. cbv beta. exists m3. do 14 eexists. split; [rewrite A0, HA; reflexivity|]. auto. }
  subst Q2. cbv beta. intros c3 [(m3 & q0 & q1 & q2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & q3 & q4 & q5 & q6 & E3 & MU3 & WM3 & MI3 & CH3) EMO3].
  destruct c3 as [ms3 mo3]. cbn in E3, EMO3. subst ms3 mo3.
  replace (ret_pc (Z_to_bv 64 0x2b8088)) with (Z_to_bv 64 0x2b8088) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  (* [comment removed for export] *)
  assert (HR3 : RHEAP s' ((p', A', n') :: LB) m3).
  { eapply RHEAP_frame_proof; [exact HR2| exact MU3| exact WM3|]. constructor; [| constructor]. right. right. exists (p', A', n'). split; [left; reflexivity|]. cbn. clear -MN. lia. }
  assert (AUX3 : rauxv_ok m3 B).
  { eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [| constructor]. cbn. unfold RMallocRep.RAUXV_CELL. clear -MN RA1 RA4 RA5 HB GEO. lia. }
  assert (ST3 : stk usegs m3 lo (bv_unsigned sp + -64)).
  { eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. cbn. clear -MN RA4 GEO CLO. lia. }
  assert (ERR3 : rw_cells usegs m3 RMalloc_iface_stmt.RERRNO [C4 errv2]).
  { eapply rw_cells_transport; [rewrite <- ETP; exact ERR2| exact MU3| exact WM3|]. cbn. unfold RMalloc_iface_stmt.RERRNO. clear -MN RA1 RA5. lia. }
  assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rheap_pres_rw_cells; [exact PRES2| exact FR1|]. left. clear. lia. }
  assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. clear -MN RA4 GEO. lia. }
  (* [comment removed for export] *)
  assert (TL3 : bytes_at usegs m3 (A' + mn) (skipn (Z.to_nat mn) junk)).
  { eapply bytes_at_transport; [| exact MU3|].
    - destruct CBY as (Y0 & Y1 & YB). split; [clear -Y0 MN; lia|]. split; [rewrite length_skipn, JL; rewrite JL in Y1; clear -Y1 MN; lia|].
      intros j Hj. rewrite length_skipn, JL in Hj. replace (A' + mn + Z.of_nat j) with (A' + Z.of_nat (Z.to_nat mn + j)) by (clear -MN; lia).
      rewrite (YB (Z.to_nat mn + j)%nat) by (rewrite JL; clear -Hj MN; lia). rewrite nth_error_skipn. reflexivity.
    - rewrite length_skipn, JL. cbn. clear -MN. lia. }
  (* [comment removed for export] *)
  eapply sreach_seq.
  { eapply (cj_evt_sreach usegs _ _ mo2 (proj1 (KM_halted_lazy _ _ KM2)) (proj2 (KM_halted_lazy _ _ KM2))). apply rre_mv3_walk. }
  cbv beta. intros c4 [E4 EMO4]. destruct c4 as [ms4 mo4]. cbn in E4, EMO4. subst ms4 mo4.
  pose proof (free_sr_at rfree_entry rfree_body_proof) as FSR.
  unfold HeapSR_iface.free_sr_stmt_at in FSR. cbn [HeapSR_iface.hs_SR HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_lb_remove HS] in FSR.
  eapply sreach_seq.
  { eapply (FSR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 s' ((p', A', n') :: LB) p A n lo B errv2 mo2 HR3 KM2 ltac:(right; exact HIN) AUX3);
      rewrite ?USP; [clear -HB; lia| exact ST3| exact CLO| unfold RFREE_STACK; clear -LO; lia| rewrite ETP; exact ERR3| exact MI3| exact TP| rewrite A0; reflexivity]. }
  clear FSR. cbv beta. intros c5 POST5.
  destruct POST5 as (k0 & k1 & k2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & k3 & k4 & k5 & k6 & m4 & s'' & E5 & KM4 & VO4 & MI4 & ST4 & ERR4 & AUX4 & PRES4 & HR4).
  destruct c5 as [ms5 mo5]. cbn in E5, KM4, VO4. subst ms5. rewrite USP in ST4, PRES4.
  replace (ret_pc (Z_to_bv 64 0x2b8090)) with (Z_to_bv 64 0x2b8090) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rheap_pres_rw_cells; [exact PRES4| exact FR3|]. left. clear. lia. }
  (* [comment removed for export] *)
  eapply sreach_mono.
  { eapply (cj_evt_sreach usegs _ _ mo5 (proj1 (KM_halted_lazy _ _ KM4)) (proj2 (KM_halted_lazy _ _ KM4))).
    eapply (rre_mv4_walk _ sp gp tp k0 k1 k2 _ _ _ g1 g2 g3 g4 g5 g6 g7 _ s3 s4 s5 s6 s7 s8 s9 s10 s11 k3 k4 k5 k6 ra s0 s1 s2 s3 s4 s5 s6 F fc m4 lo);
      [clear -LO; lia| exact SPH| exact MI4| exact ST4| exact FR4]. }
  cbv beta. intros c6 [E6 EMO6]. unfold rre_mv4_post in E6.
  release_frame FR4 ST4 (bv_unsigned sp).
  (* [comment removed for export] *)
  assert (NEp : p' <> p).
  { pose proof (RHEAP_blocks_nodup_proof _ _ _ HR2) as ND. cbn [map] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _]. intros Epp. apply NI. rewrite Epp.
    apply in_map_iff. exists (p, A, n). split; [reflexivity| exact HIN]. }
  assert (LBR : lb_remove p ((p', A', n') :: LB) = (p', A', n') :: lb_remove p LB).
  { unfold lb_remove. cbn -[bptr_eqb]. destruct (bptr_eqb p' p) eqn:Eb; cbn -[bptr_eqb]; [| reflexivity].
    exfalso. apply NEp. apply bptr_eqb_eq in Eb. exact Eb. }
  cbn [HeapSR_iface.hs_RHEAP HeapSR_iface.hs_lb_remove HS] in HR4, PRES4. rewrite LBR in HR4, PRES4.
  assert (SUB : forall b, In b (lb_remove p LB) -> In b LB).
  { intros b Hb. unfold lb_remove in Hb. apply In_filter_iff in Hb. destruct Hb as [Hb _]. exact Hb. }
  (* [comment removed for export] *)
  assert (HP1 : rheap_pres (lb_remove p LB) (bv_unsigned sp) m m1).
  { intros a Ha Hc. split; [apply MU1| apply WM1]. rewrite unsigned_lit by exact Ha. cbn.
    destruct Hc as [X|[[X1 X2]|(b & Hb & Hab)]]; [clear -X; lia| clear -X1 GEO HCEILB; lia|].
    pose proof (RHEAP_block_range_proof s LB m b ltac:(exists st, LB0; split; [exact PERM|]; split; [exact Hst|]; split; [exact RM|]; split; [split; [exact BLK| exact AR]| exact RZ]) (SUB _ Hb)) as (_ & _ & _ & R4 & _).
    unfold MallocBlocks.blk_addr, MallocBlocks.blk_size in R4. unfold RMalloc_iface_stmt.blk_addr, RMalloc_iface_stmt.blk_size in Hab. clear -Hab R4 GEO. lia. }
  assert (HP3 : rheap_pres (lb_remove p LB) (bv_unsigned sp) m2 m3).
  { intros a Ha Hc. split; [apply MU3| apply WM3]. rewrite unsigned_lit by exact Ha. cbn.
    destruct Hc as [X|[[X1 X2]|(b & Hb & Hab)]]; [clear -X MN RA4 GEO; lia| clear -X1 MN RA1 RA5; lia|].
    destruct (fresh_block_disjoint_client _ RHEAP_block_range_proof RHEAP_blocks_disjoint_proof RHEAP_blocks_nodup_proof s' LB m2 p' A' n' (bv_unsigned sp) a 1 HR2
               ltac:(right; right; exists b; split; [exact (SUB _ Hb)|]; clear -Hab; lia) ltac:(clear -GEO; lia) ltac:(clear; lia)); clear -H MN; lia. }
  assert (HP : rheap_pres (lb_remove p LB) (bv_unsigned sp) m m4).
  { eapply rheap_pres_trans; [exact HP1|]. eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact PRES2| clear; lia| exact SUB]|].
    eapply rheap_pres_trans; [exact HP3|]. eapply rheap_pres_weaken; [exact PRES4| clear; lia|]. intros b Hb. right. exact Hb. }
  (* [comment removed for export] *)
  assert (CH3' : rw_cells usegs m3 A' [CB (Z.to_nat mn) (firstn (Z.to_nat mn) pre); CB (Z.to_nat (n' - mn)) (skipn (Z.to_nat mn) junk)]).
  { apply rw_cells_CB2; [rewrite firstn_length_le by (clear -MN LEN; lia); reflexivity| rewrite length_skipn, JL; clear -MN; lia| |].
    - apply bytes_at_app. split; [pose proof (proj2 (proj1 CH3)) as X; cbn [cells_bytes cbytes app] in X; rewrite app_nil_r in X; exact X|].
      rewrite firstn_length_le by (clear -MN LEN; lia). rewrite Z2Nat.id by (clear -MN; lia). exact TL3.
    - replace (Z.of_nat (Z.to_nat mn + Z.to_nat (n' - mn))) with (Z.of_nat (Z.to_nat n')) by (clear -MN; lia). eapply wr_at_transport; [exact CWR| exact WM3]. }
  assert (CH4 : rw_cells usegs m4 A' [CB (Z.to_nat mn) (firstn (Z.to_nat mn) pre); CB (Z.to_nat (n' - mn)) (skipn (Z.to_nat mn) junk)]).
  { eapply rheap_pres_rw_cells; [exact PRES4| exact CH3'|]. right. right. exists (p', A', n'). split; [left; reflexivity|]. cbn. clear -MN. lia. }
  (* [comment removed for export] *)
  unfold HeapSR_iface.realloc_sr_post.
  cbn [HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_lb_remove HS].
  exists k0, k1, k2, g1, g2, g3, g4, g5, g6, g7, k3, k4, k5, k6, m4, errv2, A', (skipn (Z.to_nat mn) junk), p', s''.
  split; [exact E6|]. split; [rewrite EMO6; exact KM4|]. split; [rewrite EMO6; eapply vm_only_trans; [exact VO2| exact VO4]|].
  split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|]. split; [exact HP|].
  split; [exact RNG2|]. split; [exact HR4|].
  replace (Z.min n n') with mn by (subst mn; apply Z.min_comm). exact CH4.
Qed.

Theorem realloc_sr : HeapSR_iface.realloc_sr_stmt HS.
Proof. try hcb. try hsb.
  unfold HeapSR_iface.realloc_sr_stmt, HeapSR_iface.realloc_sr_stmt_at.
  cbn [HeapSR_iface.hs_SR HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_alloc_ok HeapSR_iface.hs_lb_remove HS].
  intros until mo. intros HR KMs HIN AOK BY LEN AUX HB ST CLO LO ERR MI TP A0 A1 N.
  pose proof KMs as (Lk & CRk & Kk & Bk).
  (* [comment removed for export] *)
  eapply (cj_evt_sreach_k usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b7cd0) fc None m (seg_rom usegs))
            _ mo _ (kb_halt _ _ _ Kk) (proj1 (kb_minv _ _ _ Kk))).
  { unfold HeapSR_iface.RREALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  (* [comment removed for export] *)
  destruct HR as (st & LB0 & PERM & Hst & RM & [BLK AR] & RZ).
  assert (HIN0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact HIN]).
  destruct (areach_inv _ _ _ AR) as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR HIN0) as (k & Hk & (C1 & C2 & C3)). destruct k as [[c off] nn]. cbn [MallocBlocks.blk_slot MallocBlocks.blk_size MallocBlocks.blk_addr bslot bsize boff fst snd] in C1, C2, C3. subst nn.
  destruct (MI_WFree.block_facts x0 st L BL LS INV c off n Hk) as (mm & bm & i & ai & aa & ar & ka & BF).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as CI.
  assert (HO : hosts st bm mm) by (exists ai; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)).
  pose proof (ci_gmetas _ _ CI bm mm HO) as GO.
  destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r & Hr & Kr).
  assert (SECR : 0 <= c_secret (Malloc.ctx st) < 2 ^ 64).
  { destruct (ia_secret _ (proj1 (proj2 INV))) as [SR [(_ & Z0 & _)|(_ & E1)]]; unfold Malloc.ctx; [rewrite Z0; clear; lia| rewrite E1; exact SR]. }
  assert (HA : A = bk_P c off r).
  { rewrite C3. unfold bk_P. rewrite (conc_region' st c r) by (rewrite (bk_c st c off n mm bm i ai aa ar ka BF); exact Hr). reflexivity. }
  destruct (rinplace n' (bk_E st c mm r - bk_P c off r) (bk_sc st mm)) eqn:IP.
  - eapply (realloc_inplace_sr ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n n' lo B pre errv mo
              st LB0 L BL LS c off mm bm i ai aa ar ka r); try eassumption; try reflexivity.
    + exact (ci_ticks _ _ CI).
    + exact (ci_nodup _ _ CI).
  - eapply (realloc_move_sr ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n n' lo B pre errv mo
              st LB0 L BL LS c off mm bm i ai aa ar ka r); try eassumption; try reflexivity.
    + exact (ci_ticks _ _ CI).
    + exact (ci_nodup _ _ CI).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma alloc_ok_le s LB n n' : alloc_ok s LB n -> 0 <= n' <= n -> alloc_ok s LB n'.
Proof.
  intros (A0 & A1 & A2 & A3) Hn. unfold alloc_ok. split; [lia|]. split; [lia|]. split; [exact A2|].
  unfold HeapSR_iface.big1 in *. destruct (Z.ltb_spec HeapSR_iface.BIGB n'); destruct (Z.ltb_spec HeapSR_iface.BIGB n); lia.
Qed.

Lemma lbrm_notin LB blk : ~ In (blk_slot blk) (map blk_slot LB) -> lbrm LB blk = LB.
Proof.
  induction LB as [|b LB IH]; intros NI; cbn; [reflexivity|].
  destruct (aptr_eqb (blk_slot b) (blk_slot blk)) eqn:E; cbn.
  - exfalso. apply NI. left. apply aptr_eqb_eq in E. exact E.
  - f_equal. apply IH. intros X. apply NI. right. exact X.
Qed.

Theorem aalloc_sr : HeapSR_iface.aalloc_sr_stmt HS.
Proof. try hcb. try hsb.
  unfold HeapSR_iface.aalloc_sr_stmt, HeapSR_iface.aalloc_sr_stmt_at.
  cbn [HeapSR_iface.hs_SR HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_alloc_ok HeapSR_iface.hs_lb_remove HS].
  intros until mo. intros HR KMs AOK AUX HB ST CLO LO ERR MI TP A0 A1 (k & HK & HAL) N1 N.
  pose proof KMs as (Lk & CRk & Kk & Bk).
  unfold HeapSR_iface.RAALLOC_STACK, RMALLOC_STACK in LO. unfold HeapSR_iface.RMMAP_THRESHOLD in N. unfold HeapSR_iface.RAALLOC_SYM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof AUX as (av0 & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & AVB).
  assert (SPH : bv_unsigned sp + 8 <= 2 ^ 64) by (clear -AVB HB; lia). clear AVB av0 x3 x4 x5 x16 x6 x11 x12 x23 rnd.
  assert (ALR : 16 <= al <= 64).
  { rewrite HAL. split; [change 16 with (2^4); apply Z.pow_le_mono_r; clear -HK; lia| change 64 with (2^6); apply Z.pow_le_mono_r; clear -HK; lia]. }
  assert (ETP : errno_addr tp = RMalloc_iface_stmt.RERRNO) by (rewrite TP; unfold errno_addr, RMalloc_iface_stmt.RATP, RMallocRep.RATP, RMalloc_iface_stmt.RERRNO; rewrite unsigned_lit by (clear; lia); reflexivity).
  pose proof HR as (st & LB0 & PERM & Hst & RM & [BLK AR] & RZ).
  (* [comment removed for export] *)
  eapply sreach_seq.
  { eapply (cj_evt_sreach usegs _ _ mo (kb_halt _ _ _ Kk) (proj1 (kb_minv _ _ _ Kk))).
    eapply (raa_pro_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo al n);
      [exact A0| exact A1| exists k; split; [exact HK| exact HAL]| exact N1| unfold MMAP_THRESHOLD; clear -N; lia| exact RZ| exact ST| clear -CLO HCEILB; lia| clear -LO; lia| exact MI]. }
  cbv beta. intros c1 [(a2' & m1 & junk & E1 & FR1 & ST1 & MU1 & WM1 & MI1) EMO1].
  destruct c1 as [ms1 mo1]. cbn in E1, EMO1. subst ms1 mo1.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; clear -LO CLO SPR HCEILB; lia).
  assert (HR1 : RHEAP s LB m1).
  { eapply RHEAP_frame_proof; [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. clear -LO CLO. lia. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. constructor; [| constructor]. cbn. unfold RMallocRep.RAUXV_CELL. clear -HB LO CLO HCEILB. lia. }
  rewrite ETP in ERR.
  assert (ERR1 : rw_cells usegs m1 RMalloc_iface_stmt.RERRNO [C4 errv]).
  { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold RMalloc_iface_stmt.RERRNO. clear -LO CLO HCEILB. lia. }
  (* [comment removed for export] *)
  pose proof (malloc_sr_at_off P2 rmalloc_entry RMALLOC_STACK rmalloc_body) as MSR.
  eapply sreach_seq.
  { eapply (MSR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB (n + al - 16) lo B errv mo HR1 KMs (alloc_ok_le s LB (n + al) (n + al - 16) AOK ltac:(clear -N1 ALR; lia)) AUX1);
      rewrite ?USP; [clear -HB; lia| exact ST1| exact CLO| unfold RMALLOC_STACK; clear -LO; lia| rewrite ETP; exact ERR1| exact MI1| exact TP| reflexivity| unfold HeapSR_iface.RMMAP_THRESHOLD; clear -N N1 ALR; lia]. }
  clear MSR. cbv beta. intros c2 POST2.
  destruct POST2 as (v0 & v1 & v2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & v3 & v4 & v5 & v6 & m2 & errv2 & A & junk2 & p & s' & E2 & KM2 & VO2 & MI2 & ST2 & ERR2 & AUX2 & PRES2 & RNG2 & HR2 & CH2 & OFF & CLSP).
  destruct c2 as [ms2 mo2]. cbn in E2, KM2, VO2. subst ms2. rewrite USP in ST2, PRES2.
  replace (ret_pc (Z_to_bv 64 0x2b7a8c)) with (Z_to_bv 64 0x2b7a8c) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra]).
  { eapply rheap_pres_rw_cells; [exact PRES2| exact FR1|]. left. clear. lia. }
  set (n0 := n + al - 16) in *.
  (* [comment removed for export] *)
  pose proof HR2 as (st' & LB0' & PERM' & Hst' & RM' & [BLK' AR'] & RZ').
  assert (HIN0 : In (p, A, n0) LB0') by (eapply Permutation_in; [apply Permutation_sym; exact PERM'| left; reflexivity]).
  destruct (areach_inv _ _ _ AR') as (L & LS & BL & INV & _ & _ & _ & CR).
  destruct (Forall2_In_l _ _ _ _ CR HIN0) as (kb & Hk & (C1 & C2 & C3)). destruct kb as [[c off] nn]. cbn [MallocBlocks.blk_slot MallocBlocks.blk_size MallocBlocks.blk_addr bslot bsize boff fst snd] in C1, C2, C3. subst nn.
  destruct (MI_WFree.block_facts x0 st' L BL LS INV c off n0 Hk) as (mm & bm & i & ai & aa & ar & ka & BF).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR') as CI.
  assert (HO : hosts st' bm mm) by (exists ai; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)).
  pose proof (ci_gmetas _ _ CI bm mm HO) as GO. pose proof (ci_ticks _ _ CI) as TK. pose proof (ci_nodup _ _ CI) as ND0.
  destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r & Hr & Kr).
  assert (SECR : 0 <= c_secret (Malloc.ctx st') < 2 ^ 64).
  { destruct (ia_secret _ (proj1 (proj2 INV))) as [SR [(_ & Z0 & _)|(_ & E1')]]; unfold Malloc.ctx; [rewrite Z0; clear; lia| rewrite E1'; exact SR]. }
  assert (HA : A = bk_P c off r).
  { rewrite C3. unfold bk_P. rewrite (conc_region' st' c r) by (rewrite (bk_c st' c off n0 mm bm i ai aa ar ka BF); exact Hr). reflexivity. }
  assert (O255 : off <= 255).
  { destruct OFF as (o & Ho & EA). rewrite C3, <- C1 in EA. unfold MallocBlocks.blk_slot in EA. cbn [fst] in EA.
    rewrite <- Hst', conc_strip in EA. unfold UNIT in EA. clear -EA Ho. lia. }
  pose proof RM' as (WF' & _).
  destruct (bk_all st' L BL LS c off n0 mm bm i ai aa ar ka r INV Hk BF Hr WF')
    as ((B0 & BAL & S0 & S16 & SPAN & BC) & (Hi & Hoff & Hn & Hfit & R0 & RS & B3) & [SK SKL] & SC & [ST16 STM] & G63 & SST & DRr & _).
  unfold UNIT, IB in Hfit, RS, SC.
  assert (SC48 : bk_sc st' mm < 48).
  { destruct (Z.lt_ge_cases (bk_sc st' mm) 48) as [LT|GE]; [exact LT|]. exfalso. pose proof (G63 GE) as E63.
    pose proof (is_small _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ _ Hk (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) ltac:(exact E63)) as BIG.
    cbn [bsize snd] in BIG. unfold MMAP_THRESHOLD in BIG. clear -BIG N ALR. subst n0. lia. }
  (* [comment removed for export] *)
  assert (CLS' : 27 <= bk_sc st' mm -> 2028 < n).
  { intros H27.
    assert (LE1 : bk_sc st' mm <= size_to_class n0 + 1).
    { assert (EC1 : fst p = c) by exact C1.
      pose proof (CLSP mm i) as Q. rewrite <- Hst', s_slots_strip, !get_meta_rec_strip, EC1 in Q.
      exact (Q (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) SC48). }
    destruct (Z.le_gt_cases n0 2716) as [LE|GT]; [| clear -GT ALR; subst n0; lia].
    pose proof (MI_Cnt.size_to_class_small n0 ltac:(clear -LE N1 ALR; subst n0; lia)) as S25. clear -H27 LE1 S25. lia. }
  pose proof (SST SC48) as SST'.
  set (P := bk_P c off r) in *. set (E := bk_E st' c mm r) in *. set (stride := bk_stride st' mm) in *.
  assert (EP : P = r_base r + snd c + 16 * off) by reflexivity.
  assert (EE : E = r_base r + snd c + stride - 4) by reflexivity.
  assert (GEO : 16 <= r_base r + snd c /\ r_base r + snd c <= P /\ P + n0 <= E /\ E + 4 <= hceil /\ hceil + 8224 <= bv_unsigned sp)
    by (rewrite EP, EE; clear -B0 S0 SC SK SKL SPAN BC Hoff Hfit Hn CLO LO ST16 EP EE; lia).
  (* [comment removed for export] *)
  eapply sreach_mono.
  { eapply (cj_evt_sreach usegs _ _ mo2 (proj1 (KM_halted_lazy _ _ KM2)) (proj2 (KM_halted_lazy _ _ KM2))).
    eapply (raa_fix_evt st' L BL LS c off n0 mm bm i ai aa ar ka r INV BF Hr GO SECR
              (Z_to_bv 64 0x2b7a8c) ra sp gp tp v0 v1 v2 _ _ _ y1 y2 y3 y4 y5 y6 y7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 s0 s1 F fc m2 junk lo n al k);
      [exact RM'| exact MI2| exact ST2| exact CLO| clear -LO; lia| exact SPH| exact FR2| rewrite HA; reflexivity| reflexivity| reflexivity| exact HAL| exact HK| exact N1| subst n0; clear; lia| exact SC48]. }
  cbv beta. intros cf [POST EMO]. unfold raa_fix_post, raa_tail_post in POST.
  destruct POST as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & Ems & MI3).
  fold P in Ems, MI3. set (adj := aadj P al) in *. set (m3 := raa_fix_mem st' c off n0 mm bm i r m2 n al) in *.
  pose proof RNG2 as (RA1 & RA2 & RA3 & RA4 & RA5). rewrite HA in RA2.
  pose proof (aadj_facts P al k HAL HK RA2) as (ADR & AD16 & ADAL & _ & AL16). fold adj in ADR, AD16, ADAL.
  assert (A16' : adj <= al - 16) by (clear -ADR AD16 AL16; Z.div_mod_to_equations; lia).
  assert (HBm : conc st' bm = r_base r + snd bm) by (apply conc_region'; exact Hr).
  set (C2 := fun a => r_base r + snd c - 4 <= a < E).
  (* [comment removed for export] *)
  assert (STEP : exists W off', off' = off + adj / 16 /\ P + adj = r_base r + snd c + 16 * off' /\ 0 <= off' <= 258
            /\ rmrep (relay st' W c off' n) m3 /\ ticks_ok (relay st' W c off' n) /\ relay_ok st' c W off' n /\ rpres_except C2 m2 m3).
  { destruct (Z.eq_dec adj 0) as [AZ|ANZ].
    - exists (ss_list c off n stride i), off.
      destruct (rre_inplace_rep st' L BL LS c off n0 mm bm i ai aa ar ka r INV BF Hr m2 n RM' TK ltac:(clear -N1; lia) ltac:(unfold UNIT, IB; subst n0; clear -Hfit ALR; lia) SC48 CLS')
        as (RMx & TKx & ROKx & _).
      assert (EM3 : m3 = rre_ss_mem m2 P E n (bk_b3 st' c off n0 mm i r)).
      { subst m3. unfold raa_fix_mem. fold P adj. rewrite AZ. reflexivity. }
      rewrite EM3. split; [rewrite AZ; clear; lia|]. split; [rewrite AZ, EP; clear; lia|]. split; [clear -Hoff; lia|].
      split; [exact RMx|]. split; [exact TKx|]. split; [exact ROKx|].
      apply (rpres_rre_ss C2 m2 m2 P E n); [apply rpres_except_refl| clear -GEO; lia| clear -N1; lia| clear -GEO N1 ALR; subst n0; lia| clear -GEO HCEILB; lia
        | rewrite EE, EP; clear -SST' Hoff N1; lia| subst C2; cbv beta; clear -GEO Hoff EP N1 ALR; subst n0; lia| subst C2; cbv beta; intros x Hx; clear -Hx GEO N1; lia].
    - exists (aa_list c (off + adj / 16) n stride i (aa_q c (off + adj / 16) bm)), (off + adj / 16).
      assert (A16 : 16 <= adj <= al - 16) by (clear -ADR AD16 AL16 ANZ; Z.div_mod_to_equations; lia).
      assert (ED : adj = 16 * (adj / 16)) by (clear -AD16 A16; Z.div_mod_to_equations; lia).
      destruct (raa_aa_rep st' L BL LS c off n0 mm bm i ai aa ar ka r INV BF Hr m2 n adj RM' TK N1 ltac:(clear -A16; lia) AD16
                  ltac:(unfold UNIT, IB; subst n0; clear -Hfit A16; lia) ltac:(clear -O255 A16 ALR ED Hoff; lia) SC48 CLS') as (RMx & TKx & ROKx & _).
      assert (EM3 : m3 = raa_mem m2 (P + adj) E n (r_base r + snd c) i ((P + adj - conc st' bm - 16) / 16)).
      { subst m3. unfold raa_fix_mem. fold P adj E. replace (adj =? 0) with false by (symmetry; apply Z.eqb_neq; exact ANZ). reflexivity. }
      rewrite EM3. split; [reflexivity|]. split; [rewrite EP; clear -ED; lia|]. split; [clear -O255 A16 ALR ED Hoff; lia|].
      split; [exact RMx|]. split; [exact TKx|]. split; [exact ROKx|].
      apply (rpres_raa C2 m2 m2 (P + adj) E n (r_base r + snd c) i); [apply rpres_except_refl| clear -GEO; lia| rewrite EP; clear -Hoff A16; lia| clear -N1; lia
        | clear -GEO A16 ALR; subst n0; lia| clear -GEO HCEILB; lia| rewrite EE, EP; clear -SST' Hoff N1 A16; lia
        | subst C2; cbv beta; intros x Hx; clear -Hx GEO ALR N1; subst n0; lia| subst C2; cbv beta; intros x Hx; clear -GEO Hx Hoff A16 EP ALR N1; subst n0; lia
        | subst C2; cbv beta; intros x Hx; clear -Hx GEO A16 N1; lia]. }
  clear Hfit.
  destruct STEP as (W & off' & EOFF & EA' & OFF' & RM3 & TK3 & ROK & PE3).
  set (st3 := relay st' W c off' n) in *.
  assert (STRIP : strip st3 = strip st') by apply strip_relay.
  assert (CONC : forall q, conc st3 q = conc st' q) by (intros q; apply conc_relay).
  assert (REG : s_regions st3 = s_regions st') by exact (MI_Ext.ce_regions _ _ (proj1 (relay_ctrl st' W c off' n))).
  assert (CTX : Malloc.ctx st3 = Malloc.ctx st') by exact (MI_Ext.ce_ctx _ _ (proj1 (relay_ctrl st' W c off' n))).
  (* [comment removed for export] *)
  assert (NCimg : forall a, 0x2c5000 <= a < 0x358000 -> ~ C2 a).
  { intros a Ha. subst C2. cbv beta. clear -GEO Ha CLO LO DRr EP EE B0 S0 SC SK SKL SPAN HCEILB Hoff Hn ST16 N. intros X; lia. }
  assert (NChi : forall a, lo <= a -> ~ C2 a).
  { intros a Ha. subst C2. cbv beta. clear -GEO Ha CLO. intros X; lia. }
  assert (SLOTp : ~ In (blk_slot (p, A, n0)) (map blk_slot LB)).
  { pose proof (NoDup_map_perm _ _ _ PERM' ND0) as ND1. cbn [map] in ND1. apply List.NoDup_cons_iff in ND1. exact (proj1 ND1). }
  assert (NCblk : forall b a, In b LB -> blk_addr b <= a < blk_addr b + blk_size b -> ~ C2 a).
  { intros b a Hb Hab.
    assert (Hb0 : In b LB0') by (eapply Permutation_in; [apply Permutation_sym; exact PERM'| right; exact Hb]).
    destruct (Forall2_In_l _ _ _ _ CR Hb0) as (kb & Hk' & (K1 & K2 & K3)).
    assert (NEk : bslot kb <> c).
    { rewrite <- K1, <- C1. intros E0. apply SLOTp. rewrite <- E0. apply in_map. exact Hb. }
    destruct (bk_blk_sep st' L BL LS c off n0 mm bm i ai aa ar ka r INV BF Hr WF' kb Hk' NEk) as [D|D];
      rewrite <- K3 in D; rewrite <- ?K2 in D; subst C2; cbv beta; unfold RMalloc_iface_stmt.blk_addr, RMalloc_iface_stmt.blk_size in Hab;
      unfold MallocBlocks.blk_addr, MallocBlocks.blk_size in D; fold E in D; clear -D Hab; intros X; lia. }
  assert (HP3 : rheap_pres LB (bv_unsigned sp) m2 m3).
  { intros a Ha Hc. apply PE3; [exact Ha|]. destruct Hc as [X|[[X1 X2]|(b & Hb & Hab)]]; [apply NChi; clear -X LO; lia| apply NCimg; exact X1| eapply NCblk; [exact Hb| exact Hab]]. }
  assert (HP1 : rheap_pres LB (bv_unsigned sp) m m1).
  { intros a Ha Hc. split; [apply MU1| apply WM1]. rewrite unsigned_lit by exact Ha. cbn.
    destruct Hc as [X|[[X1 X2]|(b & Hb & Hab)]]; [clear -X; lia| clear -X1 LO CLO HCEILB; lia|].
    pose proof (RHEAP_block_range_proof s LB m b HR Hb) as (_ & _ & _ & R4 & _).
    unfold MallocBlocks.blk_addr, MallocBlocks.blk_size in R4. unfold RMalloc_iface_stmt.blk_addr, RMalloc_iface_stmt.blk_size in Hab. clear -Hab R4 LO CLO. lia. }
  assert (HP : rheap_pres LB (bv_unsigned sp) m m3).
  { eapply rheap_pres_trans; [exact HP1|]. eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact PRES2| clear; lia| intros b Hb; exact Hb]| exact HP3]. }
  (* [comment removed for export] *)
  assert (ERR3 : rw_cells usegs m3 RMalloc_iface_stmt.RERRNO [C4 errv2]).
  { eapply rpres_except_rw_cells; [exact PE3| rewrite <- ETP; exact ERR2|]. cbn. intros a Ha. apply NCimg. unfold RMalloc_iface_stmt.RERRNO in Ha. clear -Ha. lia. }
  assert (AUX3 : rauxv_ok m3 B).
  { eapply rauxv_ok_pres_B; [exact AUX2| exact PE3| intros a Ha; apply NChi; clear -Ha HB LO CLO; lia| intros a Ha; apply NCimg; unfold RMallocRep.RAUXV_CELL, RMalloc_iface_stmt.RAUXV_CELL in Ha; clear -Ha; lia]. }
  assert (RZ3 : rstatic_zero m3).
  { unfold rstatic_zero in *. eapply rpres_except_rw_cells; [exact PE3| exact RZ'|]. cbn. intros a Ha. apply NCimg. unfold RMalloc_iface_stmt.RCTX, RMallocRep.RCTX in Ha. clear -Ha. lia. }
  assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra]).
  { eapply rpres_except_rw_cells; [exact PE3| exact FR2|]. cbn. intros a Ha. apply NChi. clear -Ha LO. lia. }
  assert (ST3 : stk usegs m3 lo (bv_unsigned sp + -32)).
  { eapply rpres_except_stk; [exact PE3| exact ST2|]. intros a Ha. apply NChi. clear -Ha. lia. }
  release_frame FR3 ST3 (bv_unsigned sp).
  (* [comment removed for export] *)
  destruct (ruser_chunk st3 m3 (fst c, snd c + 16 * off') r n RM3 ltac:(rewrite REG, (bk_c st' c off n0 mm bm i ai aa ar ka BF); exact Hr)
              (bk_Kr st' L BL LS c off n0 mm bm i ai aa ar ka r INV BF Hr) ltac:(cbn [snd]; clear -GEO OFF' SC S0 SK; lia)
              ltac:(cbn [snd]; rewrite EOFF; clear -GEO EP EE SC SPAN SKL ADR AD16 AL16 ALR Hoff N1 O255; subst n0; Z.div_mod_to_equations; lia) ltac:(clear -N1; lia)) as (junk3 & CH3).
  rewrite CONC, (conc_region' st' (fst c, snd c + 16 * off') r) in CH3 by (rewrite (bk_c st' c off n0 mm bm i ai aa ar ka BF); exact Hr). cbn [snd] in CH3.
  replace (r_base r + (snd c + 16 * off')) with (P + adj) in CH3 by (rewrite EA'; clear; lia).
  (* [comment removed for export] *)
  unfold HeapSR_iface.aalloc_sr_post.
  cbn [HeapSR_iface.hs_KREL HeapSR_iface.hs_MPRES HeapSR_iface.hs_RHEAP HeapSR_iface.hs_rauxv_ok HeapSR_iface.hs_lb_remove HS].
  exists u0, u1, u2, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m3, errv2, (P + adj), junk3, (c, off'), s'.
  split; [exact Ems|]. split; [rewrite EMO; exact KM2|]. split; [rewrite EMO; exact VO2|].
  split; [exact MI3|]. split; [exact ST3|]. split; [rewrite ETP; exact ERR3|]. split; [exact AUX3|]. split; [exact HP|].
  split. { unfold rblock_range. split; [clear -GEO ADR; lia|]. split; [rewrite <- Zplus_mod_idemp_l, RA2, <- Zplus_mod_idemp_r, AD16; reflexivity|].
           split; [clear -N1; lia|]. split; [clear -GEO ADR A16' ALR N1; subst n0; lia|]. rewrite HA in RA5. fold P in RA5. clear -RA5 ADR A16' ALR N1 GEO. subst n0. lia. }
  split; [exact ADAL|].
  split; [| exact CH3].
  (* [comment removed for export] *)
  exists st3, (((c, off'), conc st' c + UNIT * off', n) :: lbrm LB0' (p, A, n0)).
  split. { replace (conc st' c + UNIT * off') with (P + adj).
           2:{ rewrite EA', (conc_region' st' c r) by (rewrite (bk_c st' c off n0 mm bm i ai aa ar ka BF); exact Hr). unfold UNIT. clear; lia. }
           apply perm_skip. eapply Permutation_trans; [apply lbrm_perm; exact PERM'|].
           unfold lbrm at 1. rewrite filter_cons_False by (rewrite aptr_eqb_refl; intros X; exact X).
           fold (lbrm LB (p, A, n0)). rewrite (lbrm_notin LB (p, A, n0) SLOTp). apply Permutation_refl. }
  split; [rewrite STRIP; exact Hst'|]. split; [exact RM3|]. split; [split|].
  3:{ exact RZ3. }
  - unfold brk_link in BLK' |- *. rewrite CTX. destruct (Malloc.c_brk (Malloc.ctx st')); try exact BLK'. rewrite CONC. exact BLK'.
  - subst st3. rewrite <- C1. unfold lbrm. apply (areach_relay st' LB0' (p, A, n0) W off' n AR' HIN0). rewrite C1. exact ROK.
Qed.
End Realloc.

End HCW.
