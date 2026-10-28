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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I1_defs Fz_I1_rep Fz_I1_getrn. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_I1_insert1 Fz_I1_retrieve Fz_I2_ppi. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_K_hash Fz_K_rep Fz_K_getrn.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_LH_RETRIEVE : Z := 0xea164.

Definition plh_retrieve_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B items : Z) (bks : list (list pnode)) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (lh + 96, lh + 100)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ plh_rep m' LBall L lh pl pb B items bks.

(* [comment removed for export] *)
Theorem plh_retrieve_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (s : PState) (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B items : Z) (bks : list (list pnode)) (d S lo : Z) (str : list byte) (m0 : mem),
  RHEAP s LBall m0 -> plh_rep m LBall L lh pl pb B items bks ->      (* [comment removed for export] *)
  rw_cells usegs m d [C8 (Z_to_bv 64 S)] -> (d + 8 <= lo \/ bv_unsigned sp <= d) -> (d + 8 <= lh + 96 \/ lh + 100 <= d) ->
  0 < S -> bytes_at usegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 40 ->
  (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> (S + Z.of_nat (length str) + 1 <= lh + 96 \/ lh + 100 <= S) ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 d ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - LHR_STACK -> bv_unsigned sp mod 16 = 0 -> d mod 8 = 0 -> 0 < d -> mem_inv usegs m ->
  evt usegs (plh_retrieve_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L lh pl pb B items bks)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_LH_RETRIEVE) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until m0. intros HP REP DC DLOC DLH S0 STR NONUL NE LEN SLOC SLH HASHES -> -> ST CLO SLO SAL DAL DPOS MI.
  unfold LHR_STACK, GETRN_STACK, FZ_LH_RETRIEVE in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof REP as (OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN16 & IT & CH & EMP & ND).
  unfold lh_cells, PROP_FNS, PROP_GEO, lf_comp, lf_hash, lf_hashw, lf_compw, MallocRep.wz in SC. cbn [g_nn g_na g_p g_pmax g_items] in SC.
  pose proof (rw_cells_bound _ _ _ _ DC) as DB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in DB.
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  set (h := lh_strhash str) in *. set (idx := h mod 8) in *.
  pose proof (lh_strhash_range str) as HR. assert (IDXR : 0 <= idx < 8) by (subst idx; apply Z.mod_pos_bound; lia).
  (* [comment removed for export] *)
  assert (REPAT : forall mc (err' : word), munch [(bv_unsigned sp - 128, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc -> wmono usegs m mc ->
    rw_cells usegs mc lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 985744); C8 (Z_to_bv 64 985692); C8 (Z_to_bv 64 987044); C8 (Z_to_bv 64 987076); C8 x40; C8 x48;
                          C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 items); C4 err'; C4 pad] ->
    plh_rep mc LBall L lh pl pb B items bks).
  { intros mc err' MUc WMc SCc. eapply (plh_rep_errw s m0 _ m mc); [exact HP| exact REP| exact MUc| exact WMc| | exact SCc].
    intros a Ha Hn. cbn [outside]. lia. }
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (lh + 96, lh + 100)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (cown_al8 _ _ _ _ _ _ _ _ HP OL) as (LAL & _). pose proof (cown_al8 _ _ _ _ _ _ _ _ HP OB) as (BAL & _).
  (* [comment removed for export] *)
  assert (TAIL : forall (err' y : word) (mc : mem) (jf : list byte),
    rw_cells usegs mc lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 985744); C8 (Z_to_bv 64 985692); C8 (Z_to_bv 64 987044); C8 (Z_to_bv 64 987076); C8 x40; C8 x48;
                          C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 items); C4 err'; C4 pad] ->
    rw_cells usegs mc d [C8 (Z_to_bv 64 S)] -> bytes_at usegs mc S (str ++ [Z_to_bv 8 0]) ->
    rw_cells usegs mc (bv_unsigned sp + -32) [CB 16 jf; C8 s0; C8 ra] -> stk usegs mc lo (bv_unsigned sp + -32) ->
    munch [(bv_unsigned sp - 128, bv_unsigned sp); (lh + 96, lh + 100)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    evt usegs (plh_retrieve_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L lh pl pb B items bks)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 lh) (Z_to_bv 64 d) y a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xea18c) fc None mc (seg_rom usegs))).
  { intros err' y mc jf SCc DCc STRc FR STc MUc WMc MIc.
    do 2 step.
    apply (rw_cells_split_CB usegs _ _ [] 16 _ _ [8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (cb8_c8_in' _ _ [CB 8 _] _ _) in FR. cbn [app] in FR.
    lazymatch type of FR with rw_cells _ _ _ [CB 8 ?j; C8 ?hs; C8 s0; C8 ra] =>
      change [CB 8 j; C8 hs; C8 s0; C8 ra] with ([CB 8 j] ++ [C8 hs] ++ [C8 s0; C8 ra]) in FR end.
    apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR. destruct FR as [FR0 FR]. apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR. destruct FR as [FRH FRS].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRH, FRS.
    replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in * by lia. replace (bv_unsigned sp + -24 + 8) with (bv_unsigned sp + -16) in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (REPAT mm err' ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as REPc end.
    calle (eapply (pgetrn_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBall L lh pl pb B items bks d S (bv_unsigned sp + -24) lo str _ s m0));
      try (unfold GETRN_STACK; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    lazymatch goal with H : munch _ m mq |- _ => rename H into MUq end. lazymatch goal with H : wmono usegs m mq |- _ => rename H into WMq end.
    lazymatch goal with H : rw_cells usegs mq lh _ |- _ => rename H into SCq end.
    pose proof (REPAT mq err' MUq WMq SCq) as REPq. pose proof REPq as (_ & _ & _ & _ & _ & _ & _ & CHq & _ & _).
    pose proof (CHq idx ltac:(lia)) as (cend & SEGq & TERMq). rewrite <- (plseg_end _ _ _ _ _ _ SEGq) in *.
    pose proof (rw_cells_bound _ _ _ _ TERMq) as TB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in TB.
    assert (CAL : cend mod 8 = 0).
    { rewrite (plseg_end _ _ _ _ _ _ SEGq).
      lazymatch goal with |- pend ?c ?ns mod 8 = 0 => destruct (pend_where ns c) as [[_ ->]|(pre & p & A & hh & E1 & ->)] end;
      [ clear - BAL; Z.div_mod_to_equations; lia
      | pose proof (plseg_owns _ _ _ _ _ _ SEGq ((p, A), hh) ltac:(rewrite E1; apply in_or_app; right; left; reflexivity)) as OWq; cbn [fst snd] in OWq;
        destruct (cown_al8 _ _ _ _ _ _ _ _ HP OWq) as (QAL & _); clear - QAL; Z.div_mod_to_equations; lia ]. }
    step. step. ubs_if. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
    lazymatch goal with F0 : rw_cells usegs mq (bv_unsigned sp + -32) [CB 8 ?jj], FH : rw_cells usegs mq (bv_unsigned sp + -24) [C8 ?hv], FS : rw_cells usegs mq (bv_unsigned sp + -16) _ |- _ =>
      assert (FJ : rw_cells usegs mq (bv_unsigned sp + -32) ([CB 8 jj] ++ [C8 hv] ++ [C8 s0; C8 ra]));
      [ apply rw_cells_app; split; [exact F0|]; apply rw_cells_app; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
        replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by lia; replace (bv_unsigned sp + -24 + 8) with (bv_unsigned sp + -16) by lia; split; [exact FH| exact FS]
      | clear F0 FH FS ] end.
    cbn [app] in FJ.
    do 2 step. lazymatch goal with STh : stk _ mq _ _ |- _ => release_frame FJ STh (bv_unsigned sp) end. step. step.
    apply evt_done. unfold plh_retrieve_post. do 14 eexists. exists mq. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption. }
  step. carve_frame 32%nat ST. do 3 step. step. ubs_if. step. step. ubs_if. step. step. if_cases K.
  - eapply TAIL; eassumption.
  - cstep. eapply TAIL; eassumption.
Qed.
End WithCeiling0.
