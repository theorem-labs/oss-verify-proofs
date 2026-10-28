(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I3_base Fz_I3_kit Fz_I3_fxi Fz_W3_iface Fz_W3_defs Fz_T_ekit
     Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_clear_free Fz_M_secure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_W1_defs Fz_W1_sync Fz_W1_new Fz_W1_free Fz_W2_rep Fz_W2_exd Fz_W5_env.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation wz := (Z_to_bv 64) (only parsing).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma meth_destroy : forall m meth, cimg m -> mem_inv usegs m -> (meth = M_MEM \/ meth = M_SECMEM) -> rw_cells usegs m (meth + 80) [C8 (wz FZ_MEM_FREE)].
Proof.
  intros m meth CIMG MI [-> | ->]; unfold M_MEM, M_SECMEM, FZ_MEM_FREE.
  - cimg_cell CIMG m (0x2d3fc8 + 80) [C8 (wz 0x183a50)] H. exact H.
  - cimg_cell CIMG m (0x2d4038 + 80) [C8 (wz 0x183a50)] H. exact H.
Qed.

(* [comment removed for export] *)
Lemma w_nonneg : forall n, 0 <= wA n /\ 0 <= wB n /\ 0 <= wBig n.
Proof. intros n. unfold wA, wB, wBig. destruct (Z.leb_spec n TIER_A_MAX); destruct (Z.ltb_spec TIER_A_MAX n); unfold TIER_A_MAX in *; lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bfree_tail : crypto_free_stmt ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB LBL : list block) (L : @clist bptr) (f : nat) (K : mbk) (BI E lo B : Z)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (st1 : PState) (LB1 : list block) (L1 : @clist bptr) (f1 : nat)
         (junk : list byte) (EVr : nat) (rem : list bptr),
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - (32 + 32 + 32 + 32 + 32 + 64 + 16 + 8192) -> incl_blocks LBL LBall -> (forall b, In b LBL -> ~ mbio_T K (blk_id b)) ->
  cstate st1 LB1 LB L1 m1 (wz (bv_unsigned sp + -64)) tp lo B ->
  cframe (mbio_T K) [] (bv_unsigned sp) s LBall L m st1 LB1 L1 m1 ->
  libenv m1 LBL E ->
  cown LB1 L1 (k_bi K) BI 128 128 ->
  rw_cells usegs m1 (BI + 112) [C8 z64; C8 z64] ->
  rw_cells usegs m1 (bv_unsigned sp + -32) [CB 12 junk; C4 (wz 0); C8 s0; C8 ra] ->
  rw_cells usegs m1 (bv_unsigned sp + -64) [C8 s2; C8 s1; C8 sp; C8 (wz 0x10b908)] ->
  (f - EVr <= f1)%nat -> (1 <= f1)%nat -> (EVr + 1 = length (mbio_blocks K))%nat -> cgrow L L1 0 0 0 ->
  (forall q, In q (mbio_blocks K) <-> k_bi K = q \/ In q rem) -> ~ In (k_bi K) rem ->
  (forall b, In b LB1 <-> In b LBall /\ ~ In (blk_id b) rem) ->
  (forall q nm, In (q, nm) L1 <-> In (q, nm) L /\ ~ In q rem) ->
  climpl f1 L1 st1
    (MS (mkR (wz 0x10b9d0) (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (bv_unsigned sp + -32)) (wz BI) a0 a1 a2 a3 a4 a5 a6 a7 (wz 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x10b9d0) fc None m1 (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (mbio_T K) [] (length (mbio_blocks K)) 0 0 0
       (fun v LBall' L' m' => v = wz 1 /\ libenv m' LBL E
            /\ (forall b, In b LBall' <-> (In b LBall /\ ~ In (blk_id b) (mbio_blocks K))) /\ (forall q nm, In (q, nm) L' <-> (In (q, nm) L /\ ~ In q (mbio_blocks K))))).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CF. intros until rem. intros CST SLO INCL NTL CST1 FR1 ENV1 OWNI EXD FRo FRi FU1 F1 EVR GR1 HREM NREM HLB1 HL1.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  pose proof CST1 as (HP1 & _ & (errv1 & _ & SPB1 & ST1 & LO1 & _ & MI1 & _) & LXS1 & _ & CIMG1 & GLO1).
  pose proof FR1 as (CFR1 & KP1 & _).
  assert (TPV : bv_unsigned tp = RATP) by (rewrite TP; apply unsigned_lit; unfold RATP; lia). unfold RATP in TPV.
  unfold GLOBALS_TOP, ceil_window in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (USP1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia). rewrite USP1 in ST1, SPB1.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNI)) as (BI0 & BI16 & _ & BICL & BIIMG).
  (* [comment removed for export] *)
  destruct (libenv_exd_cells _ _ _ ENV1) as (kd & LK & pk & INKL & XI & XK & HKD & XO1 & XR1 & XO2 & XR2 & XTS & XT & XG & LK0 & LKAL & XM & XIP).
  assert (INK1 : In (pk, LK, 40) LB1) by (apply (proj1 KP1); [exact (INCL _ INKL)| exact (NTL _ INKL)]).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 INK1) as (_ & _ & _ & KCL & KIMG).
  assert (NEIK : k_bi K <> pk) by (intros EQ; apply (NTL _ INKL); cbn [blk_id fst]; rewrite <- EQ; left; reflexivity).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNI) INK1 NEIK) as APIK.
  unfold DC_S, DC_GLOBAL_LOCK, DC_IP12 in XI, XK, XO1, XR1, XO2, XR2, XG, XIP. unfold TSD_MAIN, RATP in XTS, XT. change (3344744 + -88) with 3344656 in XTS.
  change (3333808 + 4) with 3333812 in XK. change (3333808 + 8) with 3333816 in XO1. change (3333808 + 12) with 3333820 in XR1.
  change (3333808 + 16) with 3333824 in XO2. change (3333808 + 20) with 3333828 in XR2.
  unfold mutex_cells in XM. set (Pk := 3480784 + 8 * kd) in *.
  pose proof (munch_refl [(bv_unsigned sp - 64 - 384, bv_unsigned sp + -64); (BI + 112, BI + 128)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. ths. ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch goal with MUh : munch _ m1 mc, WMh : wmono usegs m1 mc |- _ =>
      assert (LXSc : lx_statics mc)
        by (eapply lx_statics_agree; [exact (agree_on_of_munch _ _ _ MUh WMh)| | exact LXS1];
            intros a Ha; cbv beta; cbn [outside]; unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha; clear - Ha GLO SLO RSP BIIMG BI0; lia) end end.
  pose proof T_freeex_proof as X. unfold T_freeex_stmt, FREEEX_STACK, DC_IP12, DC_GLOBAL_LOCK, DC_S, GLOBALS_TOP, mutex_cells in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 3480784 kd LK (BI + 112)).
  all: try first [reflexivity | eassumption | rewrite TPV; eassumption | clear - TPV HKD BI0 BI16 BICL BIIMG KCL KIMG APIK LO SLO GLO RSP; lia].
  clear X. cbv beta delta [mkR].
  ths. ths. ths. ths. ths. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mc1 end.
  lazymatch goal with H : stk usegs mc1 lo _ |- _ => rename H into STc end. lazymatch goal with H : mem_inv usegs mc1 |- _ => rename H into MIc end.
  lazymatch goal with H : munch _ m1 mc1 |- _ => rename H into MUc end. lazymatch goal with H : wmono usegs m1 mc1 |- _ => rename H into WMc end.
  lazymatch goal with H : rw_cells usegs mc1 (bv_unsigned sp + -32) _ |- _ => rename H into FRoc end.
  lazymatch goal with H : rw_cells usegs mc1 (bv_unsigned sp + -64) _ |- _ => rename H into FRic end.
  assert (CSTc : cstate st1 LB1 LB L1 mc1 (Z_to_bv 64 (bv_unsigned sp + -64)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 mc1 _ _ tp lo B (bv_unsigned sp)); [exact CST1| exact MUc| exact WMc| exact MIc| | clear - SLO LO; lia| exact SPB| | rewrite USP1; exact STc| rewrite USP1; exact SPB1].
    - apply Forall_cons; [apply cwin_stack; clear - SLO LO; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact (proj1 OWNI)| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO GLO BIIMG BI0; lia. }
  assert (FRc : cframe (mbio_T K) [] (bv_unsigned sp) s LBall L m st1 LB1 L1 mc1).
  { eapply cframe_seg; [exact FR1| exact MUc| exact WMc| exact HP1| clear - SLO LO; lia|].
    apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact (proj1 OWNI)| | cbn; lia| cbn; lia].
    intros b0 _ NT. cbn [blk_id fst]. intros EQ. apply NT. rewrite EQ. left. reflexivity. }
  pose proof CF as CF'. unfold crypto_free_stmt in CF'.
  eapply climpl_seq.
  { eapply (CF' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc1 st1 LB1 LB L1 f1 (k_bi K) BI 128 128 lo B);
      [exact F1| exact OWNI| exact CSTc| rewrite USP1; unfold CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & -> & idx & HN & ->).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite USP1 in FRM2.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FRoc ltac:(clear - RSP; lia)) as FRo2.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FRic ltac:(clear - RSP; lia)) as FRi2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & SPB2 & ST2 & LO2 & _ & MI2 & _) & _). rewrite USP1 in ST2.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix. ths. ths. do 5 ths. th_release FRi2 (bv_unsigned sp + -32). ths.
  do 3 ths. th_release FRo2 (bv_unsigned sp). ths. chere.
  lazymatch goal with H : stk usegs m2 lo (bv_unsigned sp) |- _ => rename H into STf end.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [NDB1 NDL1].
  assert (INBK : In (k_bi K) (mbio_blocks K)) by (unfold mbio_blocks; cbn [app]; left; reflexivity).
  apply climpl_done.
  exists (Z_to_bv 64 1), m2, (lb_remove (k_bi K) LB1).
  split; [unfold cret; do 14 eexists; reflexivity|].
  split; [clear - FU1 FU2 EVR; lia|].
  split; [pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) as GR; pose proof (w_bounds 128 ltac:(lia)) as WB; clear - GR WB; unfold cgrow in *; lia|].
  split. { eapply (cstate_seg [] _ _ _ _ m2 m2 _ sp tp lo B (bv_unsigned sp)); [exact CST2| apply munch_refl| apply wmono_refl| exact MI2| apply Forall_nil| clear - SLO LO; lia| exact SPB| cbn; exact I| exact STf| exact SPB]. }
  split. { eapply cframe_call; [exact FRc| exact FRM2| clear - RSP; lia| intros a X; exact X|]. intros q _ NT EQ. apply NT. rewrite <- EQ. left. reflexivity. }
  split; [reflexivity|].
  split. { eapply libenv_agree; [exact ENV1|]. eapply agree_on_trans.
    - eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MUc WMc)|]. intros a Ha; cbv beta; cbn [outside].
      destruct (libenv_fp_where LBL a Ha) as [(X1 & X2 & X3)|(b & Hb & Hr)]; [clear - X1 SLO GLO BIIMG BI0; lia|].
      destruct b as [[q A] n]. assert (Hb1 : In (q, A, n) LB1) by (apply (proj1 KP1); [exact (INCL _ Hb)| exact (NTL _ Hb)]).
      pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 Hb1) as (_ & _ & _ & BCL & _). cbn [blk_addr blk_size fst snd] in Hr.
      assert (NEq : k_bi K <> q) by (intros EQ; apply (NTL _ Hb); cbn [blk_id fst]; rewrite <- EQ; left; reflexivity).
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 (proj1 OWNI) Hb1 NEq) as AP. clear - Hr BCL LO SLO AP; lia.
    - eapply agree_on_mono; [exact CFR2|]. intros a Ha.
      destruct (libenv_fp_where LBL a Ha) as [(X1 & X2 & X3)|(b & Hb & Hr)]; [right; right; split; [exact X1|]; split; [exact X2|]; split; [exact X3| cbn; intros X9; exact X9]|].
      right; left. exists b. split; [apply (proj1 KP1); [exact (INCL _ Hb)| exact (NTL _ Hb)]|]. split; [| exact Hr].
      intros EQ. apply (NTL _ Hb). rewrite <- EQ. left. reflexivity. }
  assert (CRI : forall q nm, In (q, nm) (cremove idx L1) <-> In (q, nm) L1 /\ q <> k_bi K).
    { intros q' nm'. destruct (cremove_split L1 idx _ HN) as (l1 & l2 & EL & _ & EC). rewrite EC. split.
      - intros Hin. split; [rewrite EL; apply in_app_or in Hin; apply in_or_app; destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; exact Hin]|].
        intros ->. pose proof NDL1 as ND'. rewrite EL, map_app in ND'. cbn [map fst] in ND'. pose proof (List.NoDup_remove_2 _ _ _ ND') as NI. apply NI.
        rewrite <- map_app. apply in_map_iff. exists (k_bi K, nm'). split; [reflexivity| exact Hin].
      - intros [Hin NE]. rewrite <- EC. exact (cremove_keep L1 idx (k_bi K) 128 q' nm' HN Hin NE). }
  split.
  - intros b. rewrite lb_remove_In, HLB1, HREM. split.
    + intros [[H1 H2] H3]. split; [exact H1|]. intros [X|X]; [exact (H3 (eq_sym X))| exact (H2 X)].
    + intros [H1 H2]. split; [split; [exact H1| intros X; apply H2; right; exact X]|]. intros X. apply H2. left. symmetry. exact X.
  - intros q nm. rewrite (CRI q nm), HL1, HREM. split.
    + intros [[H1 H2] H3]. split; [exact H1|]. intros [X|X]; [exact (H3 (eq_sym X))| exact (H2 X)].
    + intros [H1 H2]. split; [split; [exact H1| intros X; apply H2; right; exact X]|]. intros X. apply H2. left. symmetry. exact X.
Qed.

Lemma nodup_cremove : forall (L0 : @clist bptr) i x, List.NoDup (map fst L0) -> nth_error L0 i = Some x -> List.NoDup (map fst (cremove i L0)).
Proof.
  intros L0 i x ND HN. destruct (cremove_split L0 i _ HN) as (l1 & l2 & EL & _ & EC). rewrite EC. rewrite EL, map_app in ND. cbn [map] in ND.
  rewrite map_app. exact (List.NoDup_remove_1 _ _ _ ND).
Qed.
Lemma L_rm1 : forall (L L0 : @clist bptr) i (p : bptr) nm0 (rem : list bptr),
  List.NoDup (map fst L0) -> nth_error L0 i = Some (p, nm0) ->
  (forall q nm, In (q, nm) L0 <-> In (q, nm) L /\ ~ In q rem) ->
  (forall q nm, In (q, nm) (cremove i L0) <-> In (q, nm) L /\ ~ In q (p :: rem)).
Proof.
  intros L L0 i p nm0 rem ND HN H q nm. destruct (cremove_split L0 i _ HN) as (l1 & l2 & EL & _ & EC). rewrite EC. split.
  - intros Hin. assert (Hin0 : In (q, nm) L0) by (rewrite EL; apply in_app_or in Hin; apply in_or_app; destruct Hin as [Hin|Hin]; [left; exact Hin| right; right; exact Hin]).
    destruct (proj1 (H q nm) Hin0) as [H1 H2]. split; [exact H1|]. intros [EQ|X]; [| exact (H2 X)]. subst q.
    pose proof ND as ND'. rewrite EL, map_app in ND'. cbn [map fst] in ND'. apply (List.NoDup_remove_2 _ _ _ ND'). rewrite <- map_app. apply in_map_iff. exists (p, nm). split; [reflexivity| exact Hin].
  - intros [H1 H2]. rewrite <- EC. apply (cremove_keep L0 i p nm0 q nm HN); [apply H; split; [exact H1| intros X; apply H2; right; exact X]| intros EQ; apply H2; left; symmetry; exact EQ].
Qed.
Lemma LB_rm1 : forall (LBall LB0 : list block) (p : bptr) (rem : list bptr),
  (forall b, In b LB0 <-> In b LBall /\ ~ In (blk_id b) rem) ->
  (forall b, In b (lb_remove p LB0) <-> In b LBall /\ ~ In (blk_id b) (p :: rem)).
Proof.
  intros LBall LB0 p rem H b. rewrite lb_remove_In, H. cbn [In]. split.
  - intros [[H1 H2] H3]. split; [exact H1|]. intros [X|X]; [exact (H3 (eq_sym X))| exact (H2 X)].
  - intros [H1 H2]. split; [split; [exact H1| intros X; apply H2; right; exact X]|]. intros X. apply H2. left. symmetry. exact X.
Qed.
(* [comment removed for export] *)
Lemma L_keep_nth : forall (L0 : @clist bptr) i (p : bptr) nm0 q nm, nth_error L0 i = Some (p, nm0) -> In (q, nm) L0 -> q <> p -> In (q, nm) (cremove i L0).
Proof. intros. eapply cremove_keep; eassumption. Qed.

Theorem bio_free_mem_proof : crypto_free_stmt -> crypto_clear_free_stmt -> crypto_secure_clear_free_stmt -> bio_free_mem_stmt libenv.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CF CCF CSCF. unfold bio_free_mem_stmt. intros until blw. intros Hf CST SLO SA ENV INCL NTL MB ->.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  pose proof (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) as ND.
  pose proof MB as (BB & RP & fl & rrw & padw & nr & nw & OWNI & NDK & METH & HEAD & W1C & FLOK & TAIL & INNER).
  destruct INNER as (rmaxw & OWNB & BBC & OWNM & OWNR & OFF & LENM & MAX31 & DD).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNI)) as (BI0 & BI16 & _ & BICL & BIIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB)) as (BB0 & _ & _ & BBCL & _).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNM)) as (BM0 & _ & _ & BMCL & _).
  (* [comment removed for export] *)
  assert (NDK' := NDK). unfold mbio_blocks in NDK'. apply NoDup_cons_iff in NDK' as [N1 NDK']. apply NoDup_cons_iff in NDK' as [N2 NDK']. apply NoDup_cons_iff in NDK' as [N3 NDK'].
  cbn [In app] in N1, N2, N3.
  assert (NE_ib : k_bi K <> k_bb K) by (intros EQ; apply N1; left; symmetry; exact EQ).
  assert (NE_im : k_bi K <> k_bm K) by (intros EQ; apply N1; right; left; symmetry; exact EQ).
  assert (NE_bm : k_bb K <> k_bm K) by (intros EQ; apply N2; left; symmetry; exact EQ).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNI) (proj1 OWNB) NE_ib) as APIB.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNI) (proj1 OWNM) NE_im) as APIM.
  assert (TPV : bv_unsigned tp = RATP) by (rewrite TP; apply unsigned_lit; unfold RATP; lia). unfold RATP in TPV.
  unfold BFREE_STACK, FZ_BIO_FREE, GLOBALS_TOP, ceil_window in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (meth_destroy m meth CIMG MI METH) as MDS. pose proof METH as METH'. unfold M_MEM, M_SECMEM in METH. unfold FZ_MEM_FREE in MDS.
  unfold bio_head in HEAD. unfold bio_tail in TAIL. unfold bio_w1_cells in W1C.
  assert (AMO : amo_aligned AW (Z_to_bv 64 (BI + 88)) = true) by (apply th_amo_aligned; [clear - BI0 BICL CEIL_RANGE__; lia| clear - BI16; Z.div_mod_to_equations; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (BI + 88, BI + 92)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  assert (HMAL : meth mod 8 = 0) by (clear - METH; destruct METH as [-> | ->]; reflexivity).
  cprefix. th_frame 32%nat [12; 4; 8; 8]%nat ST.
  do 4 ths. ths. ths.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 6 ths.
  ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1 BI0 BICL CEIL_RANGE__; lia. }
  ths. ths. ths. ubs_if. ths. ths.
  th_amo_step AMO.
  change (Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 1)))) (Z_to_bv 32 4294967295)))) with (le4 (Z_to_bv 64 0)).
  mem_after_store.
  change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
  ths. ths. th_if_lit. ths. ths. ubs_if. ths. ths. th_if_lit.
  ths. ths. ths. ths. th_if_lit.
  ths. ths. th_if_lit. ths. ths. th_if_lit.
  ths. ths. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. clear - K2 METH; lia. }
  ths. ths. ubs_if. ths. ths. th_if_lit. ths. ths. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma end.
  lazymatch goal with H : stk usegs ma lo _ |- _ => rename H into STa end. lazymatch goal with H : mem_inv usegs ma |- _ => rename H into MIa end.
  lazymatch goal with H : rw_cells usegs ma (bv_unsigned sp + -32) _ |- _ => rename H into FRoa end.
  lazymatch goal with H : rw_cells usegs ma (bv_unsigned sp + -64) _ |- _ => rename H into FRia end.
  lazymatch goal with H : rw_cells usegs ma (BI + 72) _ |- _ => rename H into TAILa end.
  lazymatch goal with H : rw_cells usegs ma (BI + 40) _ |- _ => rename H into W1Ca end.
  lazymatch goal with H : rw_cells usegs ma BB _ |- _ => rename H into BBCa end.
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -64)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ tp lo B (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | clear - SLO LO; lia| exact SPB| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; clear - SPB; lia].
    - apply Forall_cons; [apply cwin_stack; clear - SLO LO; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact (proj1 OWNI)| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO GLO BIIMG BI0; lia. }
  assert (FRa : cframe (mbio_T K) [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| clear - SLO LO; lia|].
    apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO; lia|]. apply Forall_cons; [| apply Forall_nil].
    apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact (proj1 OWNI)| | cbn; lia| cbn; lia].
    intros b0 _ NT. cbn [blk_id fst]. intros EQ. apply NT. rewrite EQ. left. reflexivity. }
  (* [comment removed for export] *)
  change ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 nr; C8 nw; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
    with ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 nr; C8 nw] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in TAILa.
  apply (proj1 (rw_cells_app usegs ma _ _ _)) in TAILa. destruct TAILa as [_ EXDa]. cbn [cells_size csize Nat.add] in EXDa.
  replace (BI + 72 + Z.of_nat 40) with (BI + 112) in EXDa by lia.
  assert (USP1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  assert (ENVa : libenv ma LBL E).
  { eapply libenv_agree; [exact ENV|]. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. intros a Ha; cbv beta; cbn [outside].
    destruct (libenv_fp_where LBL a Ha) as [(X1 & X2 & X3)|(b & Hb & Hr)]; [clear - X1 SLO GLO BIIMG BI0; lia|].
    destruct b as [[q A] n]. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (INCL _ Hb)) as (_ & _ & _ & BCL & _). cbn [blk_addr blk_size fst snd] in Hr.
    assert (NEq : k_bi K <> q) by (intros EQ; apply (NTL _ Hb); cbn [blk_id fst]; rewrite <- EQ; left; reflexivity).
    pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNI) (INCL _ Hb) NEq) as AP. clear - Hr BCL LO SLO AP; lia. }
  destruct (k_d K) as [pd|] eqn:KD.
  2:{ (* [comment removed for export] *)
    destruct DD as (MAX0 & BMC & _).
    eapply rw_cells_transport in BMC; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - APIM BMCL LO SLO; lia].
    assert (NE_mr : k_bm K <> k_rp K) by (intros EQ; apply N3; left; symmetry; exact EQ).
    assert (NE_rb : k_rp K <> k_bb K) by (intros EQ; apply N2; right; left; exact EQ).
    eapply climpl_seq.
    { eapply (W1_mem_free_spec _ _ _ _ _ _ _ (arm_nodata CF (k_bm K) BM blw (Z_to_bv 64 0) (Z_to_bv 64 (msec meth))) (pre_nodata_stack _ _ _ _ _) CF)
        with (pbi := k_bi K) (BI := BI) (nbi := 128) (pbb := k_bb K) (BB := BB) (prp := k_rp K) (RP := RP) (fl := fl);
        [clear - Hf; lia| exact CSTa| rewrite USP1; unfold MEM_FREE_STACK, MBF_STACK, BUF_FREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity
        | exact (proj1 OWNI)| lia| exact W1Ca| exact FLOK| exact OWNB| exact BBCa| exact OWNR
        | exact NE_mr| intros EQ; exact (NE_bm (eq_sym EQ))| exact NE_rb
        | split; [reflexivity|]; split; [exact OWNM|]; split; [exact BMCL| exact BMC]]. }
    intros f1 L1x st1 ms1 (v1 & m1 & LB1x & RET1 & FU1 & GR1 & CST1 & FRM1 & -> & LB1 & L1 & i1 & j1 & (ELB1 & i0 & HN0 & EL1) & HN1 & HN2 & EL' & ELB').
    subst LB1 L1 L1x LB1x.
    destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite USP1 in FRM1.
    pose proof FRM1 as (CFR1 & KP1 & _).
    assert (NIBt : ~ (k_bm K = k_bi K \/ k_bi K = k_rp K \/ k_bi K = k_bb K)).
    { intros [X|[X|X]]; [exact (NE_im (eq_sym X))| apply N1; right; right; left; symmetry; exact X| exact (NE_ib X)]. }
    pose proof (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) as NDB0. pose proof (proj2 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) as NDL0.
    eapply (bfree_tail CF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LBall LB LBL L f K BI E lo B
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 st1 _ _ f1 (take 12 junk) 3%nat [k_bb K; k_rp K; k_bm K]);
      [exact CST| exact SLO| exact INCL| exact NTL| exact CST1
      | eapply cframe_call; [exact FRa| exact FRM1| clear - RSP; lia| intros a X; exact X| intros q _ NT X; apply NT; unfold mbio_T; destruct X as [X|[X|X]]; [right; right; left; symmetry; exact X| do 3 right; left; exact X| right; left; exact X]]
      | | | | | | clear - FU1; lia| clear - FU1 Hf; lia| unfold mbio_blocks; rewrite KD; reflexivity
      | eapply cgrow_weaken; [exact GR1| | |]; pose proof (w_bounds 32 ltac:(lia)); pose proof (w_bounds 16 ltac:(lia)); lia
      | clear - KD; intros q; unfold mbio_blocks; rewrite KD; cbn [In app]; tauto
      | cbn [In]; intros [X|[X|[X|[]]]]; [exact (NE_ib (eq_sym X))| apply N1; right; right; left; exact X| exact (NE_im (eq_sym X))]
      | | ].
    - (* [comment removed for export] *)
      eapply libenv_agree; [exact ENVa|]. eapply agree_on_mono; [exact CFR1|]. intros a Ha.
      destruct (libenv_fp_where LBL a Ha) as [(X1 & X2 & X3)|(b & Hb & Hr)]; [right; right; split; [exact X1|]; split; [exact X2|]; split; [exact X3| cbn; intros X9; exact X9]|].
      right; left. exists b. split; [exact (INCL _ Hb)|]. split; [| exact Hr].
      intros X. apply (NTL _ Hb). unfold mbio_T. destruct X as [X|[X|X]]; [right; right; left; symmetry; exact X| do 3 right; left; exact X| right; left; exact X].
    - (* [comment removed for export] *)
      split.
      + apply (proj2 (lb_remove_In _ _ _)). split; [apply (proj2 (lb_remove_In _ _ _)); split; [apply (proj2 (lb_remove_In _ _ _)); split; [exact (proj1 OWNI)| cbn; exact NE_im]| cbn]| cbn; exact NE_ib].
        intros X. apply N1. right; right; left. symmetry. exact X.
      + eapply L_keep_nth; [exact HN2| eapply L_keep_nth; [exact HN1| eapply L_keep_nth; [exact HN0| exact (proj2 OWNI)| exact NE_im]|]| exact NE_ib].
        intros X. apply N1. right; right; left. symmetry. exact X.
    - (* [comment removed for export] *)
      eapply (cfr_cells_block _ _ _ _ _ _ _ _ (k_bi K, BI, 128) CFR1 EXDa (proj1 OWNI)); [exact NIBt| cbn; lia| cbn; lia].
    - exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRoa ltac:(clear - RSP; lia)).
    - exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRia ltac:(clear - RSP; lia)).
    - (* [comment removed for export] *)
      apply LB_rm1. apply LB_rm1. apply LB_rm1. intros b; split; [intros H; split; [exact H| intros []]| intros [H _]; exact H].
    - (* [comment removed for export] *)
      eapply L_rm1; [exact (nodup_cremove _ _ _ (nodup_cremove _ _ _ NDL0 HN0) HN1)| exact HN2|].
      eapply L_rm1; [exact (nodup_cremove _ _ _ NDL0 HN0)| exact HN1|].
      eapply L_rm1; [exact NDL0| exact HN0|].
      intros q nm; split; [intros H; split; [exact H| intros []]| intros [H _]; exact H]. }
  (* [comment removed for export] *)
  destruct DD as (D & nm & junkd & OWND & MAXP & BMC & _ & LJ & DB).
  cbn [In app] in N1, N2, N3. apply NoDup_cons_iff in NDK' as [N4 _]. cbn [In] in N4.
  assert (NE_id : k_bi K <> pd) by (intros EQ; apply N1; right; right; right; left; symmetry; exact EQ).
  assert (NE_md : k_bm K <> pd) by (intros EQ; apply N3; right; left; symmetry; exact EQ).
  assert (NE_mr : k_bm K <> k_rp K) by (intros EQ; apply N3; left; symmetry; exact EQ).
  assert (NE_rb : k_rp K <> k_bb K) by (intros EQ; apply N2; right; left; exact EQ).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWND)) as (D0 & _ & _ & DCL & _).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNI) (proj1 OWND) NE_id) as APID.
  eapply rw_cells_transport in BMC; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - APIM BMCL LO SLO; lia].
  eapply rw_cells_transport in DB; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; clear - APID DCL LO SLO MAXP; lia].
  rewrite <- (Z_to_bv_bv_unsigned blw) in BMC.
  assert (ARM : buf_free_arm 2 (- wA nm - wA 32) (- wB nm - wB 32) (- wBig nm - wBig 32) (fun q => q = pd \/ q = k_bm K)
                  (pre_data (msec meth) (k_bm K) BM pd D (bv_unsigned blw) max nm) (res_data (k_bm K) pd nm)).
  { destruct METH' as [EM|EM]; rewrite EM; [exact (arm_data CCF CF (k_bm K) BM pd D (bv_unsigned blw) max nm)| exact (arm_sec CSCF CF (k_bm K) BM pd D (bv_unsigned blw) max nm)]. }
  eapply climpl_seq.
  { eapply (W1_mem_free_spec _ _ _ _ _ _ _ ARM (pre_data_stack _ _ _ _ _ _ _ _) CF)
      with (pbi := k_bi K) (BI := BI) (nbi := 128) (pbb := k_bb K) (BB := BB) (prp := k_rp K) (RP := RP) (fl := fl);
      [clear - Hf; lia| exact CSTa| rewrite USP1; unfold MEM_FREE_STACK, MBF_STACK, BUF_FREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity
      | exact (proj1 OWNI)| lia| exact W1Ca| exact FLOK| exact OWNB| exact BBCa| exact OWNR
      | intros [X|X]; [apply N4; left; symmetry; exact X| apply N3; left; exact X]| intros [X|X]; [apply N2; right; right; left; symmetry; exact X| apply N2; left; symmetry; exact X]| exact NE_rb
      | ]. 
    split; [reflexivity|]. split; [exact OWNM|]. split; [exact OWND|]. split; [exact NE_md|]. split; [clear - MAXP MAX31; lia|]. split; [exact BMCL|]. split; [exact DCL|].
    split; [unfold bufmem_cells; exact BMC| exists junkd; exact DB]. }
  intros f1 L1x st1 ms1 (v1 & m1 & LB1x & RET1 & FU1 & GR1 & CST1 & FRM1 & -> & LB1 & L1 & i1 & j1 & (i0 & j0 & HN0 & HN0' & EL1 & ELB1) & HN1 & HN2 & EL' & ELB').
  subst LB1 L1 L1x LB1x.
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite USP1 in FRM1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  assert (NIBt : ~ ((k_bi K = pd \/ k_bi K = k_bm K) \/ k_bi K = k_rp K \/ k_bi K = k_bb K)).
  { intros [[X|X]|[X|X]]; [exact (NE_id X)| exact (NE_im X)| apply N1; right; right; left; symmetry; exact X| exact (NE_ib X)]. }
  pose proof (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) as NDB0. pose proof (proj2 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) as NDL0.
  eapply (bfree_tail CF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LBall LB LBL L f K BI E lo B
           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 st1 _ _ f1 (take 12 junk) 4%nat [k_bb K; k_rp K; k_bm K; pd]);
    [exact CST| exact SLO| exact INCL| exact NTL| exact CST1
    | eapply cframe_call; [exact FRa| exact FRM1| clear - RSP; lia| intros a X; exact X| intros q _ NT X; apply NT; unfold mbio_T; destruct X as [[X|X]|[X|X]]; [do 4 right; rewrite KD, X; reflexivity| right; right; left; exact X| do 3 right; left; exact X| right; left; exact X]]
    | | | | | | clear - FU1; lia| clear - FU1 Hf; lia| unfold mbio_blocks; rewrite KD; reflexivity
    | pose proof (w_nonneg 32); pose proof (w_nonneg 16); pose proof (w_nonneg nm); eapply cgrow_weaken; [exact GR1| lia| lia| lia]
    | clear - KD; intros q; unfold mbio_blocks; rewrite KD; cbn [In app]; tauto
    | cbn [In]; intros [X|[X|[X|[X|[]]]]]; [exact (NE_ib (eq_sym X))| apply N1; right; right; left; exact X| exact (NE_im (eq_sym X))| exact (NE_id (eq_sym X))]
    | | ].
  - eapply libenv_agree; [exact ENVa|]. eapply agree_on_mono; [exact CFR1|]. intros a Ha.
    destruct (libenv_fp_where LBL a Ha) as [(X1 & X2 & X3)|(b & Hb & Hr)]; [right; right; split; [exact X1|]; split; [exact X2|]; split; [exact X3| cbn; intros X9; exact X9]|].
    right; left. exists b. split; [exact (INCL _ Hb)|]. split; [| exact Hr].
    intros X. apply (NTL _ Hb). unfold mbio_T. destruct X as [[X|X]|[X|X]]; [do 4 right; rewrite KD, X; reflexivity| right; right; left; exact X| do 3 right; left; exact X| right; left; exact X].
  - split.
    + apply (proj2 (lb_remove_In _ _ _)). split; [| cbn; exact NE_ib].
      apply (proj2 (lb_remove_In _ _ _)). split; [| cbn; intros X; apply N1; right; right; left; symmetry; exact X].
      apply (proj2 (lb_remove_In _ _ _)). split; [| cbn; exact NE_im].
      apply (proj2 (lb_remove_In _ _ _)). split; [exact (proj1 OWNI)| cbn; exact NE_id].
    + eapply L_keep_nth; [exact HN2| | exact NE_ib]. eapply L_keep_nth; [exact HN1| | intros X; apply N1; right; right; left; symmetry; exact X].
      eapply L_keep_nth; [exact HN0'| | exact NE_im]. eapply L_keep_nth; [exact HN0| exact (proj2 OWNI)| exact NE_id].
  - eapply (cfr_cells_block _ _ _ _ _ _ _ _ (k_bi K, BI, 128) CFR1 EXDa (proj1 OWNI)); [exact NIBt| cbn; lia| cbn; lia].
  - exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRoa ltac:(clear - RSP; lia)).
  - exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRia ltac:(clear - RSP; lia)).
  - apply LB_rm1. apply LB_rm1. apply LB_rm1. apply LB_rm1. intros b; split; [intros H; split; [exact H| intros []]| intros [H _]; exact H].
  - eapply L_rm1; [exact (nodup_cremove _ _ _ (nodup_cremove _ _ _ (nodup_cremove _ _ _ NDL0 HN0) HN0') HN1)| exact HN2|].
    eapply L_rm1; [exact (nodup_cremove _ _ _ (nodup_cremove _ _ _ NDL0 HN0) HN0')| exact HN1|].
    eapply L_rm1; [exact (nodup_cremove _ _ _ NDL0 HN0)| exact HN0'|].
    eapply L_rm1; [exact NDL0| exact HN0|].
    intros q nm0; split; [intros H; split; [exact H| intros []]| intros [H _]; exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bio_free_null_proof : bio_free_null_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold bio_free_null_stmt. intros until B. intros CST SLO ->.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold FZ_BIO_FREE, GLOBALS_TOP, ceil_window in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  cprefix. th_frame 32%nat [12; 4; 8; 8]%nat ST.
  do 4 ths. ths. ths.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 6 ths.
  ths. th_if_lit.
  ths. ths.
  do 5 ths.
  lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -64) _ |- _ => th_release H (bv_unsigned sp + -32) end. ths.
  do 3 ths.
  lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -32) _ |- _ => th_release H (bv_unsigned sp) end. ths. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mz end.
  lazymatch goal with H : stk usegs mz lo _ |- _ => rename H into STz end. lazymatch goal with H : mem_inv usegs mz |- _ => rename H into MIz end.
  lazymatch goal with H : munch _ m mz |- _ => rename H into MUz end. lazymatch goal with H : wmono usegs m mz |- _ => rename H into WMz end.
  apply climpl_done. exists (Z_to_bv 64 0), mz, LBall.
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [apply cgrow_refl|].
  split. { eapply (cstate_seg _ _ _ _ _ m mz _ sp tp lo B (bv_unsigned sp)); [exact CST| exact MUz| exact WMz| exact MIz| | clear - SLO LO; lia| exact SPB| | exact STz| exact SPB].
    - apply Forall_cons; [apply cwin_stack; clear - SLO LO; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO GLO; lia. }
  split. { eapply cframe_seg; [apply cframe_refl| exact MUz| exact WMz| exact HP| clear - SLO LO; lia|]. apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO; lia| apply Forall_nil]. }
  split; [reflexivity|]. split; reflexivity.
Qed.

End WithCeiling0.
