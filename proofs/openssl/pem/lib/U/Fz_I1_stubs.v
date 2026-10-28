(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_realloc Fz_I1_insert Fz_I1_insert1 Fz_cimg_rom. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_T_once Fz_I1_load Fz_I1_retrieve Fz_I1_errload Fz_I1_reason.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition STUB_STACK : Z := 16 + ELC_STACK.

Definition err_stub_stmt (E T : Z) (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo)
         (bks : list (list (bptr * Z))) (pk : bptr) (LK lo Bd : Z),
  (3 * (NBASE + n) <= f)%nat -> els_room L nmb (Z.of_nat (NBASE + n)) ->
  cstate s LBall LB L m sp tp lo Bd ->
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks -> 0 <= nmb <= 8 * g_na g -> g_items g + Z.of_nat (NBASE + n) <= LH_KMAX ->
  rw_cells usegs m ERR_ONCE_CELL (err_statics LK lh) ->
  In (pk, LK, 40) LBall -> ~ lh_T pl pb bks pk -> rw_cells usegs m LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  lo <= bv_unsigned sp - STUB_STACK -> bv_unsigned sp mod 16 = 0 ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 E) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun q => q = pk \/ lh_T pl pb bks q) [] (3 * (NBASE + n)) (Z.of_nat (NBASE + n)) 1
           (LHA_MAX + 8192) (els_res LBall L lh pl pb nmb g bks (NBASE + n) pk LK)).

(* [comment removed for export] *)
Lemma stub_seg : forall (s : PState) (LBall LB : list block) (L : @clist bptr) (m : mem) (sp tp : word) (lo Bd lh : Z) (pl pb : bptr) (bks : list (list (bptr * Z))) (pk : bptr) (LK : Z),
  cstate s LBall LB L m sp tp lo Bd -> cown LBall L pl lh 104 104 -> In (pk, LK, 40) LBall -> lo <= bv_unsigned sp - 240 ->
  forall mc, munch [(bv_unsigned sp - 240, bv_unsigned sp); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
  forall (spc : Z), bv_unsigned sp - 16 <= spc <= bv_unsigned sp -> stk usegs mc lo spc ->
  cstate s LBall LB L mc (Z_to_bv 64 spc) tp lo Bd /\ cframe (fun q : bptr => q = pk \/ lh_T pl pb bks q) [] (bv_unsigned sp) s LBall L m s LBall L mc.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s LBall LB L m sp tp lo Bd lh pl pb bks pk LK CST OL INK SLO mc MUc WMc MIc spc SPC STc.
  pose proof CST as (HP & _ & (errv & _ & SPB & _ & LO & _) & _ & _ & _ & GLO). unfold GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RHEAP_block_range_proof _ _ _ (pk, LK, 40) HP INK) as (LK0 & _ & _ & LKC & LKIMG). unfold blk_addr, blk_size in LK0, LKC, LKIMG. cbn [fst snd] in LK0, LKC, LKIMG.
  pose proof (RHEAP_block_range_proof _ _ _ (pl, lh, 104) HP (proj1 OL)) as (LH0 & _ & _ & LHC & LHIMG). unfold blk_addr, blk_size in LH0, LHC, LHIMG. cbn [fst snd] in LH0, LHC, LHIMG.
  split.
  - eapply (cstate_seg _ _ _ _ _ m mc _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MUc| exact WMc| exact MIc| | lia| lia| | rewrite unsigned_lit by lia; exact STc| rewrite unsigned_lit by lia; lia].
    + constructor; [apply cwin_stack; lia|]. constructor; [eapply (cwin_block _ _ _ (pl, lh, 104)); [exact (proj1 OL)| unfold blk_addr; cbn [fst snd]; lia| unfold blk_addr, blk_size; cbn [fst snd]; lia]|].
      constructor; [eapply (cwin_block _ _ _ (pk, LK, 40)); [exact INK| unfold blk_addr; cbn [fst snd]; lia| unfold blk_addr, blk_size; cbn [fst snd]; lia]| constructor].
    + cbn [disjoint_from]. unfold LX_FLAGS. lia.
  - eapply cframe_seg; [apply cframe_refl| exact MUc| exact WMc| exact HP| lia|].
    constructor; [apply cseg_ok_stack; lia|].
    constructor; [eapply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact (proj1 OL)| intros b0 _ NT E; apply NT; right; left; exact E| unfold blk_addr; cbn [fst snd]; lia| unfold blk_addr, blk_size; cbn [fst snd]; lia]|].
    constructor; [eapply (cseg_ok_block _ _ _ _ _ (pk, LK, 40)); [exact INK| intros b0 _ NT E; apply NT; left; exact E| unfold blk_addr; cbn [fst snd]; lia| unfold blk_addr, blk_size; cbn [fst snd]; lia]| constructor].
Qed.

Lemma etab_s01 : etab 0x314b78 22. Proof. apply etab_okb_spec. vm_cast_no_check (eq_refl true). Qed.
Lemma trange_s01 : trange 0x314b78 22. Proof. intros x Hx. unfold cimg_addr, RMallocRep.RGOT_SSP. lia. Qed.

Lemma stub_s01 : err_load_const_stmt -> err_stub_stmt 0x2acbb8 0x314b78 22.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ELC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lh pl pb B nmb g bks pk LK lo Bd
         Hf ROOM CST REP NMB ITEMS HC INK NTK MC SLO SPAL.
  unfold err_load_const_stmt in ELC.
  pose proof CST as (HP & CO & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold STUB_STACK, ELC_STACK, ELE_STACK, ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, GLOBALS_TOP, ERR_ONCE_CELL, err_statics in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (RHEAP_block_range_proof _ _ _ (pk, LK, 40) HP INK) as (LK0 & _ & _ & LKC & LKIMG). unfold blk_addr, blk_size in LK0, LKC, LKIMG. cbn [fst snd] in LK0, LKC, LKIMG.
  pose proof REP as (_ & OL & RL & _).
  pose proof (RHEAP_block_range_proof _ _ _ (pl, lh, 104) HP (proj1 OL)) as (_ & _ & _ & _ & LHIMG). unfold blk_addr, blk_size in LHIMG. cbn [fst snd] in LHIMG.
  assert (APK : lh + 104 <= LK \/ LK + 40 <= lh).
  { eapply (own_apart s LBall m pl lh 104 pk LK 40 HP); [exact (proj1 OL)| exact INK|]. intros E. apply NTK. left. symmetry. exact E. }
  assert (LKS0 : lk_state s LBall L m lh pl pb B nmb g bks pk LK) by (split; [exact REP| split; [exact MC| exact CIMG]]).
  pose proof REP as (_ & _ & _ & (x40 & x48 & err & pad & SCm) & _).
  unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SCm. unfold mutex_cells in MC.
  set (TT := fun q : bptr => q = pk \/ lh_T pl pb bks q).
  pose proof (stub_seg s LBall LB L m sp tp lo Bd lh pl pb bks pk LK CST OL INK ltac:(lia)) as SEG. fold TT in SEG.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (lh + 96, lh + 100); (LK + 4, LK + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  cprefix. step. carve_frame 16%nat ST. do 3 step. do 2 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LKSa : lk_state s LBall L mm lh pl pb B nmb g bks pk LK)
      by (eapply (lk_state_at s LBall L m m mm lh pl pb B nmb g bks pk LK (bv_unsigned sp - 240) (bv_unsigned sp));
          [exact HP| exact REP| exact INK| exact NTK| exact LKS0| exact MU| exact WM| lia| unfold GLOBALS_TOP; lia
          | exists x40, x48, err, pad; unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz; exact SCm| unfold mutex_cells; exact MC]) end.
  calle (eapply reason_spec with (s := s) (LBall := LBall) (L := L) (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (pk := pk) (LK := LK) (lo := lo) (m0 := m));
    try (unfold ERS_STACK, IGI_STACK, LHR_STACK, GETRN_STACK, GLOBALS_TOP; lia).
  step. if_cases KF.
  { (* [comment removed for export] *)
    step. do 2 step. release_frame FR PC (bv_unsigned sp). step. step.
    chere. apply climpl_done. unfold cpost. eexists (Z_to_bv 64 1), _, LBall.
    split; [unfold cret; do 14 eexists; reflexivity|].
    lazymatch goal with |- context [cstate s LBall LB L ?mf _ _ _ _] => destruct (SEG mf MU WM MI0 (bv_unsigned sp) ltac:(lia) PC) as [CSTf FRf] end.
    rewrite Z_to_bv_bv_unsigned in CSTf. destruct POST as (REPf & MCf & _).
    split; [lia|]. split; [eapply cgrow_weaken; [apply cgrow_refl| | |]; unfold LHA_MAX; lia|].
    split; [exact CSTf|]. split; [exact FRf|].
    split; [reflexivity|]. exists pb, B, nmb, g, bks. split; [exact REPf|]. split; [lia|]. split; [lia|].
    split; [eapply cgrow_weaken; [apply cgrow_refl| | |]; lia|]. split; [intros q _ X; exact X|]. split; [exact MCf| exact INK]. }
  (* [comment removed for export] *)
  do 2 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into ma end.
  destruct (SEG ma MU WM MI0 (bv_unsigned sp + -16) ltac:(lia) PC) as [CSTa FRa].
  destruct POST as (REPa & MCa & _).
  chere. eapply climpl_seq.
  { eapply ELC with (T := 0x314b78) (n := 22%nat) (lh := lh) (pl := pl) (pb := pb) (B := B) (nmb := nmb) (g := g) (bks := bks) (pk := pk) (LK := LK) (lo := lo) (Bd := Bd);
      [exact Hf| exact ROOM| exact CSTa| exact REPa| exact NMB| exact ITEMS| exact etab_s01| exact (or_introl trange_s01)| unfold ERR_ONCE_CELL, err_statics; eassumption| exact INK| exact NTK| exact MCa
      | rewrite unsigned_lit by lia; unfold ELC_STACK, ELE_STACK, ELS_STACK, LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| rewrite unsigned_lit by lia; lia| reflexivity| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & RES2).
  destruct RET2 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & ->).
  cret_lit.
  pose proof FRM2 as (CFR2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR ltac:(rewrite unsigned_lit by lia; lia)) as FR2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof (munch_refl (@nil (Z * Z)) m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
  cprefix. step. do 2 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
  chere. apply climpl_done. unfold cpost. exists (Z_to_bv 64 1), m2, LBall2.
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [exact GR2|].
  split. { eapply (cstate_seg [] _ _ _ _ m2 m2 _ sp tp lo Bd (bv_unsigned sp)); [exact CST2| apply munch_refl| apply wmono_refl| exact MI2| apply Forall_nil| lia| lia| exact I| exact ST2| exact SPB]. }
  split; [| destruct RES2 as (_ & REST); split; [reflexivity| exact REST]].
  eapply cframe_call; [exact FRa| exact FRM2| rewrite unsigned_lit by lia; lia| intros a X; exact X| intros q _ X; exact X].
Qed.
End WithCeiling0.
