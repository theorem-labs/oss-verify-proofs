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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I1_defs Fz_I1_rep Fz_I1_getrn. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_I1_insert1 Fz_M_malloc Fz_I2_ppi. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_K_hash Fz_K_rep Fz_K_getrn.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_PLH_INSERT : Z := 0xe9c14.
Definition PLHI_STACK : Z := 80 + CM_STACK.

Definition plh_insert_res (lh : Z) (pl pb : bptr) (B items : Z) (bks : list (list pnode)) (h : Z) (LBall : list block) (L : @clist bptr)
    : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (pn : bptr) (N : Z), v = Z_to_bv 64 0 /\ LBall' = (pn, N, 24) :: LBall /\ L' = (pn, 24) :: L /\ rblock_range N 24
     /\ plh_rep m' LBall' L' lh pl pb B (items + 1) (lupd (Z.to_nat (h mod 8)) (nth (Z.to_nat (h mod 8)) bks [] ++ [((pn, N), h)]) bks)
     /\ (exists x40 x48 pad : word, rw_cells usegs m' lh (lh_cells PROP_FNS B (PROP_GEO (items + 1)) x40 x48 (Z_to_bv 64 0) pad)).

(* [comment removed for export] *)
Theorem plh_insert_spec : crypto_malloc_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z)
         (lh : Z) (pl pb : bptr) (B items : Z) (bks : list (list pnode)) (pdb : bptr) (Db ndb d S : Z) (str : list byte),
  (1 <= f)%nat -> croom L (wA 24) (wB 24) (wBig 24) ->
  cstate s LBall LB L m sp tp lo Bd -> lo <= bv_unsigned sp - PLHI_STACK ->
  plh_rep m LBall L lh pl pb B items bks -> items < 16 ->
  In (pdb, Db, ndb) LBall -> ~ plh_T pl pb bks pdb -> Db <= d -> d + 8 <= Db + ndb -> Db <= S -> S + Z.of_nat (length str) + 1 <= Db + ndb ->
  rw_cells usegs m d [C8 (Z_to_bv 64 S)] -> bytes_at usegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 40 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 d -> bv_unsigned sp mod 16 = 0 -> d mod 8 = 0 ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_PLH_INSERT) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (plh_T pl pb bks) [] 1 (wA 24) (wB 24) (wBig 24)
           (plh_insert_res lh pl pb B items bks (lh_strhash str) LBall L)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM. intros until str. intros Hf ROOM CST SLO REP IT16 INDB NTDB D1 D2 S1_ S2_ DC STR NONUL NE LEN HASHES -> -> SAL DAL.
  pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold PLHI_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP, FZ_PLH_INSERT in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof REP as (OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN16 & IT & CH & EMP & ND).
  unfold lh_cells, PROP_FNS, PROP_GEO, lf_comp, lf_hash, lf_hashw, lf_compw, MallocRep.wz in SC. cbn [g_nn g_na g_p g_pmax g_items] in SC.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INDB) as (Db0 & _ & _ & DbC & DbIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OL)) as (_ & _ & _ & _ & LHIMG).
  destruct (plh_sep _ _ _ _ _ _ _ _ _ _ _ HP REP) as (APLB & APN & APNN).
  assert (APDL : Db + ndb <= lh \/ lh + 104 <= Db).
  { eapply (own_apart _ _ _ pdb Db ndb pl lh 104 HP INDB (proj1 OL)). intros E. apply NTDB. left. exact E. }
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (lh_strhash_range str) as HR.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (lh + 96, lh + 100)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (cown_al8 _ _ _ _ _ _ _ _ HP OL) as (LAL & _).
  (* [comment removed for export] *)
  cprefix. step. carve_frame 80%nat ST. do 10 step. ubs_if. do 3 step. ubs_if. do 3 step.
  rewrite (zx32_small 8) by lia. ubs_if.
  do 6 step. rewrite m_divu by (rewrite unsigned_lit by lia; lia).
  rewrite (unsigned_lit items) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (items * 2 ^ 8)) by lia.
  if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. clear - K IT IT16. pose proof (Z.div_lt_upper_bound (items * 256) 8 512 ltac:(lia) ltac:(lia)). lia. }
  clear K.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB usegs _ _ [] 16 _ _ [8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  apply (cb8_c8_in' _ _ [CB 8 _] _ _) in FR. cbn [app] in FR.
  lazymatch type of FR with rw_cells _ _ _ [CB 8 ?j; C8 ?hs; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] =>
    change [CB 8 j; C8 hs; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] with ([CB 8 j] ++ [C8 hs] ++ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  apply (proj1 (rw_cells_app usegs m1 _ _ _)) in FR. destruct FR as [FR0 FR]. apply (proj1 (rw_cells_app usegs m1 _ _ _)) in FR. destruct FR as [FRH FRS].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRH, FRS.
  replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in * by lia. replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) in * by lia.
  (* [comment removed for export] *)
  lazymatch goal with H : munch _ m m1 |- _ => rename H into MU01 end. lazymatch goal with H : wmono usegs m m1 |- _ => rename H into WM01 end.
  lazymatch goal with H : rw_cells usegs m1 lh _ |- _ => rename H into SC1 end.
  (* [comment removed for export] *)
  do 4 step.
  calle (eapply (pgetrn_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBall L lh pl pb B items bks d S (bv_unsigned sp + -72) lo str _ s m));
    try (unfold GETRN_STACK; lia); try exact DAL; try (clear - SAL; Z.div_mod_to_equations; lia).
  { eapply (plh_rep_errw s m _ m m1); [exact HP| exact REP| exact MU01| exact WM01| | exact SC1]. intros a Ha Hn. cbn [outside]. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
  rename MU01 into MU02. rename WM01 into WM02.
  lazymatch goal with H : rw_cells usegs m2 (bv_unsigned sp + -72) _ |- _ => rename H into HPC end.
  lazymatch goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end. lazymatch goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
  rename SC1 into SC2.
  assert (REP2 : plh_rep m2 LBall L lh pl pb B items bks).
  { eapply (plh_rep_errw s m _ m m2); [exact HP| exact REP| exact MU02| exact WM02| | exact SC2]. intros a Ha Hn. cbn [outside]. lia. }
  pose proof REP2 as (_ & _ & _ & _ & _ & _ & _ & CH2 & _ & _).
  set (h := lh_strhash str) in *. set (idx := h mod 8) in *. assert (IDXR : 0 <= idx < 8) by (subst idx; apply Z.mod_pos_bound; lia).
  pose proof (CH2 idx ltac:(lia)) as (cend & SEG2 & TERM2).
  pose proof (plseg_end _ _ _ _ _ _ SEG2) as ERN. rewrite <- ERN in *. rename cend into rn.
  pose proof (rw_cells_bound _ _ _ _ TERM2) as RNB0. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in RNB0.
  pose proof (plseg_end_range _ _ _ _ _ _ SEG2 ltac:(lia)) as RNC.
  pose proof (cown_al8 _ _ _ _ _ _ _ _ HP OB) as (BAL & _).
  assert (CAL : rn mod 8 = 0).
  { rewrite ERN.
    lazymatch goal with |- pend ?c ?ns mod 8 = 0 => destruct (pend_where ns c) as [[_ ->]|(pre & p & A & hh & E1 & ->)] end;
    [ clear - BAL; Z.div_mod_to_equations; lia
    | pose proof (plseg_owns _ _ _ _ _ _ SEG2 ((p, A), hh) ltac:(rewrite E1; apply in_or_app; right; left; reflexivity)) as OWq; cbn [fst snd] in OWq;
      destruct (cown_al8 _ _ _ _ _ _ _ _ HP OWq) as (QAL & _); clear - QAL; Z.div_mod_to_equations; lia ]. }
  do 3 step. ubs_if. do 2 step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
  do 5 step. chere.
  (* [comment removed for export] *)
  assert (RNB : exists pr Ar nr, In (pr, Ar, nr) LBall /\ plh_T pl pb bks pr /\ Ar <= rn /\ rn + 8 <= Ar + nr /\ (Ar + nr <= lh \/ lh + 104 <= Ar) /\ 0 < Ar /\ Ar + nr <= alloc_ceiling
                 /\ (Ar + nr <= Db \/ Db + ndb <= Ar)).
  { destruct (pend_where (nth (Z.to_nat idx) bks []) (B + 8 * idx)) as [[E1 E2]|(pre & pr & Ar & hr & E1 & E2)]; rewrite <- ERN in E2.
    - exists pb, B, 128. split; [exact (proj1 OB)|]. split; [right; left; reflexivity|].
      assert (X : B + 128 <= Db \/ Db + ndb <= B) by (eapply (own_apart _ _ _ pb B 128 pdb Db ndb HP (proj1 OB) INDB); intros E; apply NTDB; right; left; symmetry; exact E). lia.
    - assert (INR : In ((pr, Ar), hr) (concat bks)) by (eapply in_concat_nthZ; rewrite E1; apply in_or_app; right; left; reflexivity).
      destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (_ & _ & INN). pose proof (INN _ INR) as INB. cbn [fst snd] in INB.
      destruct (APN _ INR) as [X1 _]. cbn [fst snd] in X1.
      pose proof (plseg_ranges _ _ _ _ _ _ SEG2 _ ltac:(rewrite E1; apply in_or_app; right; left; reflexivity)) as X2. cbn [fst snd] in X2.
      assert (X3 : Ar + 24 <= Db \/ Db + ndb <= Ar).
      { eapply (own_apart _ _ _ pr Ar 24 pdb Db ndb HP INB INDB). intros E. apply NTDB. right; right. apply in_map_iff. exists (pr, Ar). split; [exact E|]. apply in_map_iff. exists ((pr, Ar), hr). auto. }
      exists pr, Ar, 24. split; [exact INB|]. split; [right; right; apply in_map_iff; exists (pr, Ar); split; [reflexivity| apply in_map_iff; exists ((pr, Ar), hr); auto]|]. lia. }
  destruct RNB as (pr & Ar & nr & INR & TR & RN1 & RN2 & RNS & RN3 & RN4 & RND).
  assert (INL : In (pl, lh, 104) LBall) by exact (proj1 OL).
  assert (CST2 : cstate s LBall LB L m2 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m m2 _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU02| exact WM02| exact MI2| | lia| lia| | |].
    - constructor; [apply cwin_stack; lia| constructor; [| constructor]]. apply (cwin_block _ _ _ (pl, lh, 104)); [exact INL| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia.
    - rewrite unsigned_lit by lia. exact ST2.
    - rewrite unsigned_lit by lia. lia. }
  assert (FRA : cframe (plh_T pl pb bks) [] (bv_unsigned sp) s LBall L m s LBall L m2).
  { eapply cframe_seg; [apply cframe_refl| exact MU02| exact WM02| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor; [| constructor]].
    apply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact INL| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
    intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. left. reflexivity. }
  eapply climpl_seq.
  { eapply CM with (n := 24); [exact Hf| exact ROOM| lia| exact CST2| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f3 L3 st3 ms3 (v & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & (pn & An & jk & -> & -> & -> & RNG & NEW)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM3 as (CFR3 & KP3 & _). change (Z.to_nat 24) with 24%nat in NEW.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 _].
  assert (PNEW : forall q A0 n0, In (q, A0, n0) LBall -> pn <> q).
  { intros q A0 n0 Hin E. cbn [map blk_id fst] in ND3. inversion ND3 as [|xx ll NIx _]; subst xx ll. apply NIx. subst q. apply in_map_iff. exists (pn, A0, n0). auto. }
  pose proof RNG as (An0 & _ & _ & AnC & AnIMG).
  assert (AP_R : An + 24 <= Ar \/ Ar + nr <= An)
    by (eapply (own_apart _ _ _ pn An 24 pr Ar nr HP3); [left; reflexivity| right; exact INR| exact (PNEW _ _ _ INR)]).
  assert (AP_L : An + 24 <= lh \/ lh + 104 <= An)
    by (eapply (own_apart _ _ _ pn An 24 pl lh 104 HP3); [left; reflexivity| right; exact INL| exact (PNEW _ _ _ INL)]).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR0 ltac:(lia)) as FR03.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 HPC ltac:(lia)) as HPC3.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FRS ltac:(lia)) as FRS3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pr, Ar, nr) CFR3 TERM2 INR (fun X => X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as TERM3.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pl, lh, 104) CFR3 SC2 INL (fun X => X)
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as SC3.
  clear FR0 HPC FRS TERM2.
  pose proof (munch_refl [(An, An + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
  pose proof (RHEAP_block_range_proof _ _ _ _ HP3 (or_introl eq_refl)) as RRn. unfold rblock_range, blk_addr, blk_size in RRn. cbn [fst snd] in RRn.
  destruct RRn as (_ & ANAL & _).
  (* [comment removed for export] *)
  cprefix. step. if_cases K9; zify_cond K9. { exfalso. rewrite ?unsigned_lit in K9 by lia. lia. }
  do 3 step. ubs_if. do 3 step. cstep. do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
  lazymatch goal with H : stk _ m4 _ _ |- _ => rename H into ST4 end. lazymatch goal with H : mem_inv _ m4 |- _ => rename H into MI4 end.
  lazymatch goal with H : rw_cells usegs m4 lh _ |- _ => rename H into SC4 end.
  (* [comment removed for export] *)
  assert (FJ : rw_cells usegs m4 (bv_unsigned sp + -80) ([CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 (take 64 (take 72 junk)))))))))] ++ [C8 (Z_to_bv 64 h)] ++ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply rw_cells_app. split; [exact FR03|]. apply rw_cells_app. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by lia. replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) by lia. split; [exact HPC3| exact FRS3]. }
  cbn [app] in FJ. clear FR03 HPC3 FRS3.
  do 9 step. release_frame FJ ST4 (bv_unsigned sp). step.
  chere. apply climpl_done.
  exists (Z_to_bv 64 0), m4, ((pn, An, 24) :: LBall).
  assert (INN : In (pn, An, 24) ((pn, An, 24) :: LBall)) by (left; reflexivity).
  assert (INR' : In (pr, Ar, nr) ((pn, An, 24) :: LBall)) by (right; exact INR).
  assert (INL' : In (pl, lh, 104) ((pn, An, 24) :: LBall)) by (right; exact INL).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INR) as (_ & _ & _ & _ & ARIMG).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU3|]. split; [exact GR3|].
  split. { eapply (cstate_seg _ _ _ _ _ m3 m4 _ sp tp lo Bd (bv_unsigned sp)); [exact CST3| exact MU3| exact WM3| exact MI4| | lia| lia| | exact ST4| exact SPB].
    - constructor; [| constructor; [| constructor; [| constructor]]].
      + apply (cwin_block _ _ _ (pn, An, 24)); [exact INN| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      + apply (cwin_block _ _ _ (pr, Ar, nr)); [exact INR'| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      + apply (cwin_block _ _ _ (pl, lh, 104)); [exact INL'| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - AnIMG ARIMG LHIMG RN1 RN2 An0 RL. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRA| exact FRM3| lia| intros a X; exact X| intros q0 _ _ X; exact X]| exact MU3| exact WM3| exact HP3| lia|].
    constructor; [| constructor; [| constructor; [| constructor]]].
    - apply (cseg_ok_block _ _ _ _ _ (pn, An, 24)); [exact INN| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      destruct FRA as (_ & KPA & _). exact (cfresh_new _ _ _ _ _ _ KPA ND3).
    - apply (cseg_ok_block _ _ _ _ _ (pr, Ar, nr)); [exact INR'| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. exact TR.
    - apply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact INL'| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. left. reflexivity. }
  exists pn, An. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact RNG|].
  split. 2:{ exists x40, x48, pad. unfold lh_cells, PROP_FNS, PROP_GEO, lf_comp, lf_hash, lf_hashw, lf_compw, MallocRep.wz. cbn [g_nn g_na g_p g_pmax g_items]. exact SC4. }
  eapply (plh_rep_append st3 m2 m3 m4); [exact REP2| exact HP3| exact PNEW| exact IDXR| exact ERN| exact HR| lia| lia| | exact MU3| exact WM3| exact TERM3| exact NEW| ].
  - (* [comment removed for export] *)
    destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP2) as (_ & INB2 & INN2).
    eapply agree_on_mono; [exact CFR3|]. intros a [Ha|[Ha|(n & Hn & Ha)]]; right; left.
    + exists (pl, lh, 104). split; [exact INL|]. split; [intros X; exact X|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
    + exists (pb, B, 128). split; [exact INB2|]. split; [intros X; exact X|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
    + exists (fst (fst n), snd (fst n), 24). split; [exact (INN2 n Hn)|]. split; [intros X; exact X|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
  - unfold lh_cells, PROP_FNS, PROP_GEO, lf_comp, lf_hash, lf_hashw, lf_compw, MallocRep.wz. cbn [g_nn g_na g_p g_pmax g_items]. exact SC4.
Qed.
End WithCeiling0.
