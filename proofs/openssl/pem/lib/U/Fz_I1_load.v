(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_realloc Fz_I1_insert Fz_I1_insert1 Fz_cimg_rom. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac i1_static CFR H Hn :=
  assert (Hn := cfr_cells_static _ _ _ _ _ _ _ _ CFR H);
  cbn [cells_size csize Nat.add] in Hn;
  specialize (Hn ltac:(lia) ltac:(lia));
  specialize (Hn ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS;
                        cbn [rin_ivs fst snd]; lia)).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_ERR_LOAD_STRINGS : Z := 0xe7e98.
Definition ELS_STACK : Z := 48 + LHI_STACK.
(* [comment removed for export] *)
Definition ERR_LOCK_CELL : Z := 0x32e018.
Definition ERR_HASH_CELL : Z := 0x32e020.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition els_exit (sp1 gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (m : mem) (lo Bd lh : Z) (pl pb : bptr) (nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (n : nat)
    : nat -> @clist bptr -> PState -> machine_state -> Prop :=
  fun f1 L1 st1 ms1 => exists (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 : word) (m1 : mem) (LBall1 : list block)
                              (pb1 : bptr) (B1 nmb1 : Z) (g1 : lh_geo) (bks1 : list (list (bptr * Z))),
    ms1 = MS (mkR y0 sp1 gp tp y1 y2 y3 s0 y4 y5 y6 y7 y8 y9 y10 y11 y12 (Z_to_bv 64 3334160) s3 s4 s5 s6 s7 s8 s9 s10 s11 y13 y14 y15 y16)
             F (Z_to_bv 64 0xe7f04) fc None m1 (seg_rom usegs)
    /\ (f - 3 * n <= f1)%nat
    /\ cstate st1 LBall1 LB L1 m1 sp1 tp lo Bd
    /\ cframe (lh_T pl pb bks) [] (bv_unsigned sp1) s LBall L m st1 LBall1 L1 m1
    /\ lh_rep DVERR m1 LBall1 L1 ERR_FNS lh pl pb1 B1 nmb1 g1 bks1
    /\ g_items g <= g_items g1 <= g_items g + Z.of_nat n /\ nmb <= nmb1 <= 8 * g_na g1
    /\ cgrow L L1 (Z.of_nat n + (wA nmb1 - wA nmb)) (wB nmb1 - wB nmb) (wBig nmb1 - wBig nmb)
    /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ lh_T pl pb bks q -> ~ lh_T pl pb1 bks1 q).

Lemma els_loop : lh_insert_stmt -> forall (n' : nat)
    (ra sp1 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (T lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (lo Bd : Z),
  (3 * S n' <= f)%nat -> els_room L nmb (Z.of_nat (S n')) ->
  cstate s LBall LB L m sp1 tp lo Bd ->
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks -> 0 <= nmb <= 8 * g_na g -> g_items g + Z.of_nat (S n') <= LH_KMAX ->
  etab T (S n') -> trange T (S n') ->
  rw_cells usegs m ERR_HASH_CELL [C8 (Z_to_bv 64 lh)] ->
  lo <= bv_unsigned sp1 - LHI_STACK -> bv_unsigned sp1 mod 16 = 0 -> T mod 8 = 0 ->
  climpl f L s
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 T) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 3334160) (Z_to_bv 64 (-16)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xe7ee8) fc None m (seg_rom usegs))
    (els_exit sp1 gp tp s0 (Z_to_bv 64 (-16)) s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd lh pl pb nmb g bks (S n')).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros INS. unfold lh_insert_stmt in INS.
  induction n' as [|n'' IH];
    intros ra sp1 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f T lh pl pb B nmb g bks lo Bd
           Hf ROOM CST REP NMB ITEMS ETAB TR HC SLO SPAL TAL.
  all: pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  all: unfold ERR_HASH_CELL, GLOBALS_TOP in *.
  all: pose proof (lh_geo_bounds g (proj1 REP)) as GB.
  all: assert (DVT : DVERR T) by (split; [exact TAL| intros x Hx; apply TR; lia]).
  all: assert (TRNG : 0x2c0638 <= T /\ T + 32 <= 0x32e038) by (pose proof (TR T ltac:(lia)) as X; pose proof (TR (T + 31) ltac:(lia)) as Y; unfold cimg_addr, RMallocRep.RGOT_SSP in X, Y; lia).
  all: destruct ROOM as (RA & RB & RC).
  all: pose proof (w_bounds nmb ltac:(lia)) as (WA0 & WB0 & _ & WC0).
  all: assert (ROOM1 : croom L 1 1 (LHA_MAX + 8192)) by (unfold croom, LHA_MAX in *; lia).
  all: pose proof (munch_refl (@nil (Z * Z)) m) as MU; pose proof (wmono_refl usegs m) as WM.
  all: cprefix; do 3 step; chere.
  all: eapply climpl_seq;
    [ eapply INS with (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (data := T) (lo := lo) (Bd := Bd);
        [lia| exact ROOM1| exact CST| exact REP| exact NMB| lia| exact DVT| exact SLO| exact SPAL| reflexivity| reflexivity] |].
  all: intros f1 L1 st1 ms1 (v & m1 & LBall1 & RET & FU1 & GR1c & CST1 & FRM1 & (pb1 & B1 & nmb1 & g1 & bks1 & REP1 & IT1 & NMB1 & GR1 & TK1)).
  all: destruct RET as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & ->).
  all: cret_lit.
  all: pose proof FRM1 as (CFR1 & _).
  all: i1_static CFR1 HC HC1.
  all: pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _ & _ & CIMG1 & _).
  all: pose proof (img_w64_cell m1 (T + 16) CIMG1 ltac:(intros x Hx; apply TR; lia)) as NXC.
  all: pose proof (img_w64_range (T + 16)) as NXR.
  all: pose proof (munch_refl (@nil (Z * Z)) m1) as MU1; pose proof (wmono_refl usegs m1) as WM1.
  all: cprefix; step; if_cases KO; zify_cond KO; try (exfalso; rewrite ?unsigned_lit in KO by lia; clear - KO TRNG; lia).
  all: do 2 step; step; if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; rewrite ?(unsigned_lit T) by lia.
  - (* [comment removed for export] *) exfalso. cbn [etab] in ETAB. destruct ETAB as (_ & E1). exact (K E1).
  - (* [comment removed for export] *)
    chere. apply climpl_done. unfold els_exit.
    do 17 eexists. exists m1, LBall1, pb1, B1, nmb1, g1, bks1.
    split; [reflexivity|]. split; [lia|]. split; [exact CST1|]. split; [exact FRM1|]. split; [exact REP1|].
    split; [lia|]. split; [exact NMB1|]. split; [| exact TK1].
    eapply cgrow_weaken; [exact GR1| lia| lia| lia].
  - (* [comment removed for export] *)
    destruct ETAB as (E0 & E1).
    destruct (w_delta nmb nmb1 ltac:(lia)) as (WD1 & WD2 & WD3 & WD4).
    assert (ROOMi : els_room L1 nmb1 (Z.of_nat (S n''))).
    { unfold els_room, cgrow in *. destruct GR1 as (G1a & G1b & G1c). clear - RA RB RC G1a G1b G1c WD1. lia. }
    chere. eapply climpl_mono.
    { eapply (IH _ sp1 gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 st1 LBall1 LB L1 f1 (T + 16) lh pl pb1 B1 nmb1 g1 bks1 lo Bd);
        [lia| exact ROOMi| exact CST1| exact REP1| lia| lia| exact E1| apply trange_next; exact TR| exact HC1| exact SLO| exact SPAL| lia]. }
    intros f2 L2 st2 ms2 (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & m2 & LBall2 & pb2 & B2 & nmb2 & g2 & bks2
                          & -> & FU2 & CST2 & FRM2 & REP2 & IT2 & NMB2 & GR2 & TK2).
    unfold els_exit. do 17 eexists. exists m2, LBall2, pb2, B2, nmb2, g2, bks2.
    split; [reflexivity|]. split; [lia|]. split; [exact CST2|].
    split. { eapply cframe_call; [exact FRM1| exact FRM2| lia| intros a X; exact X| exact TK1]. }
    split; [exact REP2|]. split; [lia|]. split; [lia|].
    split. { eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2)| lia| lia| lia]. }
    intros q QIN NT. apply TK2; [| exact (TK1 q QIN NT)].
    destruct FRM1 as (_ & [KP1 KP2] & _).
    destruct QIN as [X|X].
    + left. apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. exact (KP1 b Hb NT).
    + right. apply in_map_iff in X. destruct X as ([q0 nm0] & <- & Hq). cbn [fst] in NT |- *. apply in_map_iff. exists (q0, nm0). split; [reflexivity| exact (KP2 q0 nm0 Hq NT)].
  - (* [comment removed for export] *) exfalso. cbn [etab] in ETAB. destruct ETAB as (_ & E1 & _). exact (E1 K).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition els_tail_post (ra sp gp tp s0o s1o s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m1 : mem) (LK : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (LK + 4, LK + 8)]%Z m1 m' /\ wmono usegs m1 m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)).

Lemma els_tail : forall (ra sp gp tp s0o s1o s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 : word) (F : bvmap 5 word) (fc : bv 32)
    (m1 : mem) (jk : list byte) (LK lo : Z),
  rw_cells usegs m1 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  rw_cells usegs m1 ERR_LOCK_CELL [C8 (Z_to_bv 64 LK)] ->
  rw_cells usegs m1 LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 16)) -> LK mod 4 = 0 -> 0 < LK -> LK + 40 <= alloc_ceiling ->
  stk usegs m1 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 -> mem_inv usegs m1 ->
  evt usegs (els_tail_post ra sp gp tp s0o s1o s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m1 LK)
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 (Z_to_bv 64 3334160) y18 s4 s5 s6 s7 s8 s9 s10 s11 y14 y15 y16 y17)
          F (Z_to_bv 64 0xe7f04) fc None m1 (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp s0o s1o s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 F fc m1 jk LK lo FR LC MC AL LK0 LKC ST CLO SLO MI.
  unfold ERR_LOCK_CELL in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
  do 6 step. release_frame FR ST (bv_unsigned sp). step. step.
  eapply evt_mono.
  { eapply T_unlock_proof with (lo := lo); rewrite ?unsigned_lit by lia; try eassumption; try lia. }
  intros ms' (b1 & b2 & b3 & m' & -> & MU' & WM' & MI' & ST' & MC'). rewrite ?unsigned_lit in * by lia.
  unfold els_tail_post. do 14 eexists. exists m'. split; [reflexivity|]. auto.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rep_over_lock : forall s LBall m m' (L : @clist bptr) lh pl pb B nmb g bks (pk : bptr) LK x y,
  RHEAP s LBall m -> lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks -> In (pk, LK, 40) LBall -> ~ lh_T pl pb bks pk ->
  munch [(x, y); (LK + 4, LK + 8)]%Z m m' -> wmono usegs m m' -> alloc_ceiling <= x ->
  lh_rep DVERR m' LBall L ERR_FNS lh pl pb B nmb g bks.
Proof.
  intros s LBall m m' L lh pl pb B nmb g bks pk LK x y HP REP INK NT MU WM HX.
  eapply lh_rep_agree; [exact REP| | intros q A n nm _ X; exact X].
  eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|].
  pose proof REP as (G & OL & RL & _ & OB & RB & LEN & CH & _ & _).
  intros a FP. cbn [outside].
  assert (BLKOUT : forall (q : bptr) A n, In (q, A, n) LBall -> lh_T pl pb bks q -> A <= a < A + n -> ~ (x <= a < y) /\ (~ (LK + 4 <= a < LK + 8) /\ True)).
  { intros q A n INQ TQ Ha. pose proof (RHEAP_block_range_proof _ _ _ (q, A, n) HP INQ) as (_ & _ & _ & QC & _). unfold blk_addr, blk_size in QC. cbn [fst snd] in QC.
    split; [lia|]. split; [| exact I]. intros Hb.
    destruct (own_apart s LBall m q A n pk LK 40 HP INQ INK ltac:(intros E; apply NT; rewrite <- E; exact TQ)); lia. }
  destruct FP as [Ha|[Ha|(p & A & Hp & Ha)]].
  - exact (BLKOUT pl lh 104 (proj1 OL) ltac:(left; reflexivity) Ha).
  - exact (BLKOUT pb B (8 * g_na g) (proj1 OB) ltac:(right; left; reflexivity) Ha).
  - apply (BLKOUT p A 24 (proj1 (lh_rep_owned _ _ _ _ _ _ _ _ _ _ _ _ REP p A Hp))); [| exact Ha].
    right; right. apply in_map_iff. exists (p, A). split; [reflexivity| exact Hp].
Qed.

Definition els_res (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (n : nat) (pk : bptr) (LK : Z)
    : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => v = Z_to_bv 64 1 /\ exists pb' B' nmb' g' bks',
    lh_rep DVERR m' LBall' L' ERR_FNS lh pl pb' B' nmb' g' bks'
    /\ g_items g <= g_items g' <= g_items g + Z.of_nat n /\ nmb <= nmb' <= 8 * g_na g'
    /\ cgrow L L' (Z.of_nat n + (wA nmb' - wA nmb)) (wB nmb' - wB nmb) (wBig nmb' - wBig nmb)
    /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ lh_T pl pb bks q -> ~ lh_T pl pb' bks' q)
    /\ rw_cells usegs m' LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ In (pk, LK, 40) LBall'.

Definition err_load_strings_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (T : Z) (n : nat) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo)
         (bks : list (list (bptr * Z))) (pk : bptr) (LK lo Bd : Z),
  (3 * n <= f)%nat -> els_room L nmb (Z.of_nat n) ->
  cstate s LBall LB L m sp tp lo Bd ->
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks -> 0 <= nmb <= 8 * g_na g -> g_items g + Z.of_nat n <= LH_KMAX ->
  etab T n -> tread T n ->
  rw_cells usegs m ERR_LOCK_CELL [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] ->
  In (pk, LK, 40) LBall -> ~ lh_T pl pb bks pk -> rw_cells usegs m LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  lo <= bv_unsigned sp - ELS_STACK -> bv_unsigned sp mod 16 = 0 -> T mod 8 = 0 -> a0 = Z_to_bv 64 T ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_ERR_LOAD_STRINGS) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun q => q = pk \/ lh_T pl pb bks q) [] (3 * n) (Z.of_nat n) 1 (LHA_MAX + 8192)
           (els_res LBall L lh pl pb nmb g bks n pk LK)).

Theorem err_load_strings_spec : lh_insert_stmt -> err_load_strings_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros INS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f T n lh pl pb B nmb g bks pk LK lo Bd
         Hf ROOM CST REP NMB ITEMS ETAB TR HC INK NTK MC SLO SPAL TAL ->.
  pose proof CST as (HP & CO & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_ERR_LOAD_STRINGS, ERR_LOCK_CELL in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (RHEAP_block_range_proof _ _ _ (pk, LK, 40) HP INK) as (LK0 & LK16 & _ & LKC & LKIMG). unfold blk_addr, blk_size in LK0, LK16, LKC, LKIMG. cbn [fst snd] in LK0, LK16, LKC, LKIMG.
  assert (AL : LK mod 4 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in LK16; [| lia]. destruct LK16 as [k ->]. exists (k * 4). lia. }
  (* [comment removed for export] *)
  destruct (tread_first m T n CIMG MI ETAB TR) as (TC & TRNG).
  pose proof (img_w64_range T) as TWR.
  unfold mutex_cells in MC.
  pose proof T_write_lock_proof as WL. unfold T_lock_stmt in WL.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (LK + 4, LK + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  cprefix. step. carve_frame 48%nat ST. do 5 step. do 3 step. step. do 2 step. step.
  calle (eapply WL with (lo := lo)); try lia.
  clear WL.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
  lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
  lazymatch goal with H : rw_cells _ ma LK _ |- _ => rename H into MCa end.
  set (TT := fun q : bptr => q = pk \/ lh_T pl pb bks q).
  assert (TPK : TT pk) by (left; reflexivity).
  assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m ma _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor; [| constructor]]. apply (cwin_block _ _ _ (pk, LK, 40)); [exact INK| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe TT [] (bv_unsigned sp) s LBall L m s LBall L ma).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    constructor; [apply cseg_ok_stack; lia| constructor; [| constructor]].
    apply (cseg_ok_block _ _ _ _ _ (pk, LK, 40)); [exact INK| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
    intros bb0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. exact TPK. }
  assert (REPa : lh_rep DVERR ma LBall L ERR_FNS lh pl pb B nmb g bks) by (eapply (rep_over_lock s LBall m ma); [exact HP| exact REP| exact INK| exact NTK| exact MU| exact WM| lia]).
  (* [comment removed for export] *)
  assert (FINISH : forall (f1 : nat) (L1 : @clist bptr) (st1 : PState) (LBall1 : list block) (m1 : mem) (pb1 : bptr) (B1 nmb1 : Z) (g1 : lh_geo) (bks1 : list (list (bptr * Z)))
      (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : word),
    (f - 3 * n <= f1)%nat -> cstate st1 LBall1 LB L1 m1 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo Bd ->
    cframe (lh_T pl pb bks) [] (bv_unsigned sp + -48) s LBall L ma st1 LBall1 L1 m1 ->
    lh_rep DVERR m1 LBall1 L1 ERR_FNS lh pl pb1 B1 nmb1 g1 bks1 ->
    g_items g <= g_items g1 <= g_items g + Z.of_nat n -> nmb <= nmb1 <= 8 * g_na g1 ->
    cgrow L L1 (Z.of_nat n + (wA nmb1 - wA nmb)) (wB nmb1 - wB nmb) (wBig nmb1 - wBig nmb) ->
    (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ lh_T pl pb bks q -> ~ lh_T pl pb1 bks1 q) ->
    climpl f1 L1 st1
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp y1 y2 y3 sp y4 y5 y6 y7 y8 y9 y10 y11 y12 (Z_to_bv 64 3334160) y17 s4 s5 s6 s7 s8 s9 s10 s11 y13 y14 y15 y16)
          F (Z_to_bv 64 0xe7f04) fc None m1 (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd TT [] (3 * n) (Z.of_nat n) 1 (LHA_MAX + 8192)
             (els_res LBall L lh pl pb nmb g bks n pk LK))).
  { intros f1 L1 st1 LBall1 m1 pb1 B1 nmb1 g1 bks1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 FU1 CST1 FRM1 REP1 IT1 NMB1 GR1 TK1.
    pose proof FRM1 as (CFR1 & [KP1 _] & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
    i1_static CFR1 HC HC1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk, LK, 40) CFR1 MCa INK NTK
                  ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size, mutex_cells; cbn [fst snd cells_size csize Nat.add]; lia)) as MC1.
    assert (INK1 : In (pk, LK, 40) LBall1) by exact (KP1 _ INK NTK).
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
    rewrite unsigned_lit in ST1 by lia.
    change [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] with ([C8 (Z_to_bv 64 LK)] ++ [C8 (Z_to_bv 64 lh)]) in HC1.
    apply (proj1 (rw_cells_app usegs m1 _ _ _)) in HC1. destruct HC1 as [LC1 _].
    eapply climpl_evt.
    { eapply (els_tail ra sp gp tp s0 s1 s2) with (LK := LK) (lo := lo); try eassumption; try lia. }
    intros ms' (b0 & b1 & b2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & b3 & b4 & b5 & b6 & m' & -> & MU' & WM' & MI' & ST' & MC').
    apply climpl_done.
    pose proof (lh_geo_bounds g1 (proj1 REP1)) as GB1.
    destruct (w_delta nmb nmb1 ltac:(lia)) as (WD1 & WD2 & WD3 & WD4).
    pose proof (w_nonneg nmb) as (_ & _ & WN3).
    assert (NTK1 : ~ lh_T pl pb1 bks1 pk) by (apply TK1; [left; apply in_map_iff; exists (pk, LK, 40); split; [reflexivity| exact INK]| exact NTK]).
    exists (Z_to_bv 64 1), m', LBall1.
    split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU1|].
    split. { eapply cgrow_weaken; [exact GR1| | |]; unfold LHA_MAX; clear - WD1 WD2 WD3 GB1 NMB1 WN3; lia. }
    split. { eapply (cstate_seg _ _ _ _ _ m1 m' _ sp tp lo Bd (bv_unsigned sp)); [exact CST1| exact MU'| exact WM'| exact MI'| | lia| lia| | exact ST'| exact SPB].
      - constructor; [apply cwin_stack; lia| constructor; [| constructor]]. apply (cwin_block _ _ _ (pk, LK, 40)); [exact INK1| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    split. { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM1| lia| intros a X; exact X|]| exact MU'| exact WM'| exact HP1| lia|].
      - intros q _ NT X. apply NT. right. exact X.
      - constructor; [apply cseg_ok_stack; lia| constructor; [| constructor]].
        apply (cseg_ok_block _ _ _ _ _ (pk, LK, 40)); [exact INK1| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
        intros bb0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. exact TPK. }
    split; [reflexivity|]. exists pb1, B1, nmb1, g1, bks1.
    split; [eapply (rep_over_lock st1 LBall1 m1 m'); [exact HP1| exact REP1| exact INK1| exact NTK1| exact MU'| exact WM'| lia]|].
    split; [exact IT1|]. split; [exact NMB1|]. split; [exact GR1|]. split; [exact TK1|]. split; [exact MC'| exact INK1]. }
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. ubs_if. step. step. ubs_if.
  step. step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    destruct n as [|n']; [| exfalso; cbn [etab] in ETAB; exact (proj1 ETAB K1)].
    chere. eapply FINISH; [lia| exact CSTa| apply cframe_refl| exact REPa| lia| lia| | intros q _ X; exact X].
    change (Z.of_nat 0) with 0. rewrite !Z.sub_diag. apply cgrow_refl.
  - destruct n as [|n']; [exfalso; cbn [etab] in ETAB; exact (K1 ETAB)|].
    change [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] with ([C8 (Z_to_bv 64 LK)] ++ [C8 (Z_to_bv 64 lh)]) in HC.
    pose proof (proj2 (proj1 (rw_cells_app usegs ma _ _ _) HC)) as HHC. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HHC.
    step. chere. eapply climpl_seq.
    { eapply (els_loop INS n') with (T := T) (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (lo := lo) (Bd := Bd);
        [lia| exact ROOM| exact CSTa| exact REPa| exact NMB| exact ITEMS| exact ETAB| exact (tread_trange _ _ TR)| exact HHC| rewrite unsigned_lit by lia; unfold LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| rewrite unsigned_lit by lia; lia| exact TAL]. }
    intros f1 L1 st1 ms1 (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & m1 & LBall1 & pb1 & B1 & nmb1 & g1 & bks1
                          & -> & FU1 & CST1 & FRM1 & REP1 & IT1 & NMB1 & GR1 & TK1).
    rewrite unsigned_lit in FRM1 by lia.
    eapply FINISH; eassumption.
Qed.
End WithCeiling0.
