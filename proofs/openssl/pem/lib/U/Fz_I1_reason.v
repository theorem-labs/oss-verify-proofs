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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_realloc Fz_I1_insert Fz_I1_insert1 Fz_cimg_rom. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_T_once Fz_I1_load Fz_I1_retrieve Fz_I1_errload.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_ERR_GET_ITEM : Z := 0xe88d0.
Definition FZ_ERR_REASON : Z := 0xe8818.
Definition IGI_STACK : Z := 32 + LHR_STACK.
Definition ERS_STACK : Z := 64 + IGI_STACK.

(* [comment removed for export] *)
Lemma lh_fp_apart : forall s DV m LBall L f lh pl pb B nmb g bks (pk : bptr) (LK : Z),
  RHEAP s LBall m -> lh_rep DV m LBall L f lh pl pb B nmb g bks -> In (pk, LK, 40) LBall -> ~ lh_T pl pb bks pk ->
  forall a, lh_fp lh B g bks a -> a < alloc_ceiling /\ (a < LK \/ LK + 40 <= a).
Proof.
  intros s DV m LBall L f lh pl pb B nmb g bks pk LK HP REP INK NTK.
  pose proof (lh_rep_owned _ _ _ _ _ _ _ _ _ _ _ _ REP) as OWN.
  destruct REP as (G & OL & _ & _ & OB & _).
  assert (BLK : forall (q : bptr) A n, In (q, A, n) LBall -> lh_T pl pb bks q -> forall a, A <= a < A + n -> a < alloc_ceiling /\ (a < LK \/ LK + 40 <= a)).
  { intros q A n IQ TQ a Ha.
    pose proof (RHEAP_block_range_proof _ _ _ (q, A, n) HP IQ) as (_ & _ & _ & C & _). unfold blk_addr, blk_size in C. cbn [fst snd] in C.
    assert (AP : A + n <= LK \/ LK + 40 <= A).
    { eapply (own_apart s LBall m q A n pk LK 40 HP); [exact IQ| exact INK|]. intros E. apply NTK. subst q. exact TQ. }
    lia. }
  intros a [Ha|[Ha|(p & A & Hp & Ha)]].
  - eapply (BLK pl lh 104); [exact (proj1 OL)| left; reflexivity| exact Ha].
  - eapply (BLK pb B (8 * g_na g)); [exact (proj1 OB)| right; left; reflexivity| exact Ha].
  - eapply (BLK p A 24); [exact (proj1 (OWN p A Hp))| right; right; apply in_map_iff; exists (p, A); auto| exact Ha].
Qed.

(* [comment removed for export] *)
Definition lk_state (s : PState) (LBall : list block) (L : @clist bptr) (m : mem) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (pk : bptr) (LK : Z) : Prop :=
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks /\ rw_cells usegs m LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ cimg m.

(* [comment removed for export] *)
Lemma lh_rep_at : forall s LBall L m0 m mc lh pl pb B nmb g bks (pk : bptr) (LK slo shi : Z),
  RHEAP s LBall m0 -> lh_rep DVERR m0 LBall L ERR_FNS lh pl pb B nmb g bks -> In (pk, LK, 40) LBall -> ~ lh_T pl pb bks pk ->
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks ->
  munch [(slo, shi); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m mc -> wmono usegs m mc -> alloc_ceiling <= slo ->
  (exists x40 x48 err pad, rw_cells usegs mc lh (lh_cells ERR_FNS B g x40 x48 err pad)) ->
  lh_rep DVERR mc LBall L ERR_FNS lh pl pb B nmb g bks.
Proof.
  intros s LBall L m0 m mc lh pl pb B nmb g bks pk LK slo shi HP REP0 INK NTK REP MUc WMc CLO SCc.
  pose proof (lh_fp_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP0 INK NTK) as FPA.
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP0) as (S_LB & S_N & _ & _).
  pose proof (agree_on_of_munch _ _ _ MUc WMc) as AGc.
  pose proof REP as (G & _ & _ & _ & _ & _ & LEN & CH & EMP & ND). pose proof (lh_geo_bounds g G) as GB.
  eapply (lh_rep_upd DVERR m mc LBall L LBall L ERR_FNS lh pl pb B nmb g g bks bks (fun _ => False) REP); try reflexivity; try assumption.
  - intros i. right. intros X. exact X.
  - intros q A n nm _ X. exact X.
  - intros i Hi [].
  - intros i Hi _. split; [reflexivity|]. eapply agree_on_mono; [exact AGc|]. intros a Ha. cbn [outside].
    assert (LI : (Z.to_nat i < length bks)%nat) by lia.
    destruct Ha as [Ha|(q & A & Hq & Ha)].
    + assert (FP : lh_fp lh B g bks a) by (right; left; lia). destruct (FPA a FP) as [AC ALK]. clear - Ha AC ALK S_LB CLO Hi. lia.
    + assert (FP : lh_fp lh B g bks a) by (right; right; exists q, A; split; [eapply in_nth_concat; exact Hq| exact Ha]).
      destruct (FPA a FP) as [AC ALK]. destruct (S_N _ q A LI Hq) as [X1 _]. clear - Ha AC ALK X1 CLO. lia.
Qed.

(* [comment removed for export] *)
Lemma lk_state_at : forall s LBall L m0 m mc lh pl pb B nmb g bks (pk : bptr) (LK slo shi : Z),
  RHEAP s LBall m0 -> lh_rep DVERR m0 LBall L ERR_FNS lh pl pb B nmb g bks -> In (pk, LK, 40) LBall -> ~ lh_T pl pb bks pk ->
  lk_state s LBall L m lh pl pb B nmb g bks pk LK ->
  munch [(slo, shi); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m mc -> wmono usegs m mc -> alloc_ceiling <= slo -> GLOBALS_TOP <= slo ->
  (exists x40 x48 err pad, rw_cells usegs mc lh (lh_cells ERR_FNS B g x40 x48 err pad)) ->
  rw_cells usegs mc LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  lk_state s LBall L mc lh pl pb B nmb g bks pk LK.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s LBall L m0 m mc lh pl pb B nmb g bks pk LK slo shi HP REP0 INK NTK (REP & _ & CI) MUc WMc CLO GLO SCc MCc.
  split; [eapply (lh_rep_at s LBall L m0 m mc); eassumption|]. split; [exact MCc|].
  pose proof (RHEAP_block_range_proof _ _ _ (pk, LK, 40) HP INK) as (_ & _ & _ & _ & LKIMG). unfold blk_addr, blk_size in LKIMG. cbn [fst snd] in LKIMG.
  pose proof REP0 as (_ & OL & _).
  pose proof (RHEAP_block_range_proof _ _ _ (pl, lh, 104) HP (proj1 OL)) as (_ & _ & _ & _ & LHIMG). unfold blk_addr, blk_size in LHIMG. cbn [fst snd] in LHIMG.
  eapply cimg_seg; [exact CI| exact MUc|]. intros a Ha. unfold cimg_addr, RMallocRep.RGOT_SSP in Ha. unfold GLOBALS_TOP in GLO. cbn [outside]. unfold ceil_window in *. lia.
Qed.

Definition get_item_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (s : PState) (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (pk : bptr) (LK : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' v,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ lk_state s LBall L m' lh pl pb B nmb g bks pk LK
    /\ (v = 0 \/ DVERR v).     (* [comment removed for export] *)

Theorem get_item_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (s : PState) (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (pk : bptr) (LK d lo : Z) (kw : word) (m0 : mem),
  RHEAP s LBall m0 -> lh_rep DVERR m0 LBall L ERR_FNS lh pl pb B nmb g bks ->      (* [comment removed for export] *)
  lk_state s LBall L m lh pl pb B nmb g bks pk LK ->
  In (pk, LK, 40) LBall -> ~ lh_T pl pb bks pk ->
  rw_cells usegs m ERR_LOCK_CELL [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] ->
  rw_cells usegs m d [C8 kw] -> bv_unsigned sp <= d ->
  a0 = Z_to_bv 64 d ->
  stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - IGI_STACK -> bv_unsigned sp mod 16 = 0 -> d mod 8 = 0 -> mem_inv usegs m ->
  evt usegs (get_item_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m s LBall L lh pl pb B nmb g bks pk LK)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_ERR_GET_ITEM) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall L lh pl pb B nmb g bks pk LK d lo kw m0
         HP REP0 (REP & MC & CI) INK NTK HC KC KLOC -> ST GLO CLO SLO SAL DAL MI.
  unfold IGI_STACK, LHR_STACK, GETRN_STACK, GLOBALS_TOP, FZ_ERR_GET_ITEM, ERR_LOCK_CELL in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (RHEAP_block_range_proof _ _ _ (pk, LK, 40) HP INK) as (LK0 & LK16 & _ & LKC & LKIMG). unfold blk_addr, blk_size in LK0, LK16, LKC, LKIMG. cbn [fst snd] in LK0, LK16, LKC, LKIMG.
  assert (AL : LK mod 4 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in LK16; [| lia]. destruct LK16 as [k ->]. exists (k * 4). lia. }
  pose proof REP as (_ & OL & RL & _).
  pose proof (RHEAP_block_range_proof _ _ _ (pl, lh, 104) HP (proj1 OL)) as (_ & _ & _ & _ & LHIMG). unfold blk_addr, blk_size in LHIMG. cbn [fst snd] in LHIMG.
  assert (APK : lh + 104 <= LK \/ LK + 40 <= lh).
  { eapply (own_apart s LBall m0 pl lh 104 pk LK 40 HP); [exact (proj1 OL)| exact INK|]. intros E. apply NTK. left. symmetry. exact E. }
  pose proof (rw_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in KB.
  pose proof (lh_fp_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP0 INK NTK) as FPA.
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP0) as (S_LB & S_N & _ & _).
  pose proof (RHEAP_block_range_proof _ _ _ (pl, lh, 104) HP (proj1 OL)) as (_ & _ & _ & LHC & _). unfold blk_addr, blk_size in LHC. cbn [fst snd] in LHC.
  (* [comment removed for export] *)
  assert (REPAT : forall mc, munch [(bv_unsigned sp - 160, bv_unsigned sp); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m mc -> wmono usegs m mc ->
    (exists x40 x48 err pad, rw_cells usegs mc lh (lh_cells ERR_FNS B g x40 x48 err pad)) ->
    lh_rep DVERR mc LBall L ERR_FNS lh pl pb B nmb g bks).
  { intros mc MUc WMc SCc. eapply (lh_rep_at s LBall L m0 m mc lh pl pb B nmb g bks pk LK (bv_unsigned sp - 160) (bv_unsigned sp)); try eassumption. lia. }
  pose proof REP as (_ & _ & _ & (x40 & x48 & err & pad & SCm) & _).
  unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SCm.
  unfold mutex_cells in MC.
  pose proof T_read_lock_proof as RL0. unfold T_lock_stmt in RL0.
  pose proof T_unlock_proof as UL0. unfold T_unlock_stmt in UL0.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. carve_frame 32%nat ST. do 4 step. do 3 step. step. do 2 step. step.
  calle (eapply RL0 with (lo := lo)); try lia.
  clear RL0. unfold mutex_cells in POST.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 2 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CIc : cimg mm) by (eapply cimg_seg; [exact CI| eassumption|]; intros a Ha; unfold cimg_addr, RMallocRep.RGOT_SSP in Ha; cbn [outside]; unfold ceil_window in *; lia);
    assert (REPc : lh_rep DVERR mm LBall L ERR_FNS lh pl pb B nmb g bks)
      by (apply REPAT; [eassumption| eassumption| exists x40, x48, err, pad; unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz; exact SCm]);
    assert (KEXc : exists kw0 : word, rw_cells usegs mm d [C8 kw0]) by (exists kw; eassumption) end.
  calle (eapply lh_retrieve_spec with (s := s) (LBall := LBall) (L := L) (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (data := d) (lo := lo) (m0 := m0));
    try (unfold LHR_STACK, GETRN_STACK, GLOBALS_TOP; lia).
  pose proof PC0 as (_ & _ & _ & (y40 & y48 & err1 & pad1 & SC1) & _).
  unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SC1.
  do 3 step. step.
  calle (eapply UL0 with (lo := lo)); try lia.
  clear UL0.
  do 6 step. release_frame FR PC (bv_unsigned sp). step. step.
  apply evt_done. unfold get_item_post. do 16 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|]. split; [| exact POST0].
  split; [apply REPAT; [exact MU| exact WM| exists y40, y48, err1, pad1; unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz; exact SC1]|].
  split; [exact POST1|].
  eapply cimg_seg; [exact CI| exact MU|]. intros a Ha. unfold cimg_addr, RMallocRep.RGOT_SSP in Ha. cbn [outside]. unfold ceil_window in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition reason_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (s : PState) (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (pk : bptr) (LK : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 (v : word) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ lk_state s LBall L m' lh pl pb B nmb g bks pk LK.     (* [comment removed for export] *)

Theorem reason_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (s : PState) (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (pk : bptr) (LK lo : Z) (m0 : mem),
  RHEAP s LBall m0 -> lh_rep DVERR m0 LBall L ERR_FNS lh pl pb B nmb g bks ->      (* [comment removed for export] *)
  lk_state s LBall L m lh pl pb B nmb g bks pk LK ->
  In (pk, LK, 40) LBall -> ~ lh_T pl pb bks pk ->
  rw_cells usegs m ERR_ONCE_CELL (err_statics LK lh) ->
  stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ERS_STACK -> bv_unsigned sp mod 16 = 0 -> mem_inv usegs m ->
  evt usegs (reason_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m s LBall L lh pl pb B nmb g bks pk LK)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_ERR_REASON) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall L lh pl pb B nmb g bks pk LK lo m0
         HP REP0 LKS INK NTK HC ST GLO CLO SLO SAL MI.
  pose proof LKS as (REPm & MC & CI).
  unfold ERS_STACK, IGI_STACK, LHR_STACK, GETRN_STACK, GLOBALS_TOP, FZ_ERR_REASON, ERR_ONCE_CELL, err_statics in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (RHEAP_block_range_proof _ _ _ (pk, LK, 40) HP INK) as (LK0 & _ & _ & LKC & LKIMG). unfold blk_addr, blk_size in LK0, LKC, LKIMG. cbn [fst snd] in LK0, LKC, LKIMG.
  pose proof REPm as (_ & OL & RL & (x40 & x48 & err & pad & SCm) & _).
  pose proof (RHEAP_block_range_proof _ _ _ (pl, lh, 104) HP (proj1 OL)) as (_ & _ & _ & _ & LHIMG). unfold blk_addr, blk_size in LHIMG. cbn [fst snd] in LHIMG.
  assert (APK : lh + 104 <= LK \/ LK + 40 <= lh).
  { eapply (own_apart s LBall m0 pl lh 104 pk LK 40 HP); [exact (proj1 OL)| exact INK|]. intros E. apply NTK. left. symmetry. exact E. }
  (* [comment removed for export] *)
  assert (LKAT : forall mc, munch [(bv_unsigned sp - 224, bv_unsigned sp); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m mc -> wmono usegs m mc ->
    (exists x40 x48 err pad, rw_cells usegs mc lh (lh_cells ERR_FNS B g x40 x48 err pad)) ->
    rw_cells usegs mc LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
    lk_state s LBall L mc lh pl pb B nmb g bks pk LK).
  { intros mc MUc WMc SCc MCc. eapply (lk_state_at s LBall L m0 m mc lh pl pb B nmb g bks pk LK (bv_unsigned sp - 224) (bv_unsigned sp)); try eassumption; unfold GLOBALS_TOP; lia. }
  assert (LOCKC : forall mm, rw_cells usegs mm 3334160 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] ->
                             rw_cells usegs mm ERR_LOCK_CELL [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]).
  { intros mm H. change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] with ([C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] ++ [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]) in H.
    exact (proj2 (proj1 (rw_cells_app usegs mm _ _ _) H)). }
  unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SCm. unfold mutex_cells in MC.
  pose proof T_run_once_done_proof as RO. unfold T_run_once_done_stmt in RO.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  assert (EPI : forall (v z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 kv : word) (mc : mem) (j0 j1 : list byte),
    rw_cells usegs mc (bv_unsigned sp + -64) [CB 8 j0] -> rw_cells usegs mc (bv_unsigned sp + -56) [C8 kv] ->
    rw_cells usegs mc (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp - 224, bv_unsigned sp); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    lk_state s LBall L mc lh pl pb B nmb g bks pk LK ->
    evt usegs (reason_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m s LBall L lh pl pb B nmb g bks pk LK)
      (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp z1 z2 z3 z4 z5 v z6 z7 z8 z9 z10 z11 z12 z13 z14 s4 s5 s6 s7 s8 s9 s10 s11 z15 z16 z17 z18)
          F (Z_to_bv 64 0xe88b0) fc None mc (seg_rom usegs))).
  { intros v z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 kv mc j0 j1 F0 FK FS STc MUc WMc MIc LKSc.
    assert (FJ : rw_cells usegs mc (bv_unsigned sp + -64) ([CB 8 j0] ++ [C8 kv] ++ [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split; [exact F0|]. apply rw_cells_app. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) by lia. replace (bv_unsigned sp + -56 + 8) with (bv_unsigned sp + -48) by lia. auto. }
    cbn [app] in FJ. clear F0 FK FS.
    do 5 step. release_frame FJ STc (bv_unsigned sp). step. step.
    apply evt_done. unfold reason_post. do 16 eexists. split; [reflexivity|].
    split; [exact MUc|]. split; [exact WMc|]. split; [exact MIc|]. split; [exact STc| exact LKSc]. }
  (* [comment removed for export] *)
  assert (FOUND : forall (v : Z) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 kv : word) (mc : mem) (j0 j1 : list byte),
    DVERR v ->
    rw_cells usegs mc (bv_unsigned sp + -64) [CB 8 j0] -> rw_cells usegs mc (bv_unsigned sp + -56) [C8 kv] ->
    rw_cells usegs mc (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp - 224, bv_unsigned sp); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    lk_state s LBall L mc lh pl pb B nmb g bks pk LK ->
    evt usegs (reason_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m s LBall L lh pl pb B nmb g bks pk LK)
      (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp z1 z2 z3 z4 z5 (Z_to_bv 64 v) z6 z7 z8 z9 z10 z11 z12 z13 z14 s4 s5 s6 s7 s8 s9 s10 s11 z15 z16 z17 z18)
          F (Z_to_bv 64 0xe88a4) fc None mc (seg_rom usegs))).
  { intros v z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 kv mc j0 j1 DV F0 FK FS STc MUc WMc MIc LKSc.
    pose proof LKSc as (_ & _ & CIc).
    assert (VR : 0 <= v /\ v + 16 <= 2^63) by (pose proof (proj2 DV v ltac:(lia)) as X0; pose proof (proj2 DV (v + 15) ltac:(lia)) as X1; unfold cimg_addr, RMallocRep.RGOT_SSP in X0, X1; lia).
    destruct (cimg_C8 mc (v + 8) CIc ltac:(intros x Hx; apply (proj2 DV); lia)) as [w SW].
    pose proof (proj1 DV) as VAL. step. step. ubs_if. step. eapply EPI; eassumption. }
  step. carve_frame 64%nat ST. do 5 step. do 8 step. step. step.
  apply (rw_cells_split_CB usegs _ _ [] 24 _ _ [8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  apply (cb8_c8_in' _ _ [CB 8 _] _ _) in FR. cbn [app] in FR.
  apply (rw_cells_app usegs _ _ [CB 8 _] _) in FR. destruct FR as [FR0 FR]. apply (rw_cells_app usegs _ _ [C8 _] _) in FR. destruct FR as [FRK FRS].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRK, FRS.
  replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in * by lia. replace (bv_unsigned sp + -56 + 8) with (bv_unsigned sp + -48) in * by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)] with ([C4 (Z_to_bv 64 2)] ++ [C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]) in HC;
    pose proof (proj1 (proj1 (proj1 (rw_cells_app usegs mm _ _ _) HC)) : ro_cells usegs mm 3334160 [C4 (Z_to_bv 64 2)]) as ONro;
    cbn [app] in HC end.
  calle (eapply RO with (lo := lo)); try lia.
  clear RO.
  do 4 step. step. if_cases KA.
  { eapply EPI; try eassumption.
    apply LKAT; [eassumption| eassumption| exists x40, x48, err, pad; unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz; exact SCm| unfold mutex_cells; exact MC]. }
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. if_cases K1; zify_cond K1. { exfalso. revert K1. vm_compute. intros X. first [discriminate X| apply X; reflexivity]. }
  do 3 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LKSc : lk_state s LBall L mm lh pl pb B nmb g bks pk LK)
      by (apply LKAT; [eassumption| eassumption| exists x40, x48, err, pad; unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz; exact SCm| unfold mutex_cells; exact MC]);
    assert (LOCKc : rw_cells usegs mm ERR_LOCK_CELL [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]) by (apply LOCKC; exact HC) end.
  calle (eapply get_item_spec with (s := s) (LBall := LBall) (L := L) (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (pk := pk) (LK := LK)
           (d := bv_unsigned sp + -56) (lo := lo) (m0 := m0)); try (unfold IGI_STACK, LHR_STACK, GETRN_STACK, GLOBALS_TOP, ERR_LOCK_CELL in *; lia).
  pose proof PC0 as (REP1 & MC1 & _). pose proof REP1 as (_ & _ & _ & (y40 & y48 & err1 & pad1 & SC1) & _). clear REP1.
  unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SC1. unfold mutex_cells in MC1.
  step. if_cases KF.
  { destruct POST0 as [E|DV]; [exfalso; subst; revert KF; vm_compute; intros X; discriminate X|].
    eapply FOUND; try eassumption. }
  (* [comment removed for export] *)
  do 3 step. step. step.
  (* [comment removed for export] *)
  lazymatch type of FRK with rw_cells _ _ _ [C8 ?kw2] => remember kw2 as key2 eqn:EK2; clear EK2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LKSd : lk_state s LBall L mm lh pl pb B nmb g bks pk LK)
      by (apply LKAT; [eassumption| eassumption| exists y40, y48, err1, pad1; unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz; exact SC1| unfold mutex_cells; exact MC1]);
    assert (LOCKd : rw_cells usegs mm ERR_LOCK_CELL [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh)]) by (apply LOCKC; exact HC) end.
  calle (eapply get_item_spec with (s := s) (LBall := LBall) (L := L) (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (pk := pk) (LK := LK)
           (d := bv_unsigned sp + -56) (lo := lo) (m0 := m0)); try (unfold IGI_STACK, LHR_STACK, GETRN_STACK, GLOBALS_TOP, ERR_LOCK_CELL in *; lia).
  step. if_cases KG.
  - eapply EPI; try eassumption.
  - destruct POST1 as [E|DV]; [exfalso; subst; revert KG; vm_compute; intros X; discriminate X|].
    eapply FOUND; try eassumption.
Qed.
End WithCeiling0.
