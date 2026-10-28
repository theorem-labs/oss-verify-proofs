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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I1_defs Fz_I1_rep Fz_I1_getrn. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_I1_insert1 Fz_I1_retrieve Fz_M_malloc Fz_I2_ppi. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_GET_DATA : Z := 0xe4970.

(* [comment removed for export] *)
Lemma get_data3_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (C lo : Z) (v : word),
  a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 3 -> 0 < C ->
  rw_cells usegs m (C + 168) [C8 v] -> (C + 176 <= lo \/ bv_unsigned sp <= C + 168) ->
  stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m -> C mod 8 = 0 ->
  evt usegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
               /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_GET_DATA) fc None m (seg_rom usegs)).
Proof.
  intros until v. intros -> -> C0 CC CLOC ST LO0 LO MI CAL. unfold FZ_GET_DATA.
  pose proof (rw_cells_bound _ _ _ _ CC) as CB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in CB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 4 ths.
  zstep. zstep. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  zstep. zstep. zstep. th_if_lit.
  do 6 zstep.
  zstep. zstep. zstep. ubs_if.
  zstep. zstep. zstep.
  do 3 ths. zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => th_release FRh (bv_unsigned sp) end.
  zstep.
  finish.
Qed.
End WithCeiling0.

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition psd_cells (LK lh1 lh2 ni vi Q1 Q2 : Z) : list cell :=
  [C8 (Z_to_bv 64 LK); C8 (Z_to_bv 64 lh1); C8 (Z_to_bv 64 lh2); C4 (Z_to_bv 64 ni); C4 (Z_to_bv 64 vi); C8 (Z_to_bv 64 Q1); C8 (Z_to_bv 64 Q2)].
Definition nmz (nm : bool) : Z := if nm then 1 else 0.
Definition t_of (nm : bool) (lh1 lh2 : Z) : Z := if nm then lh1 else lh2.
Definition pidx_off (nm : bool) : Z := if nm then 24 else 28.
(* [comment removed for export] *)
Definition pstr_frame (Ls : Z) (j8 : list byte) (s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 (Z_to_bv 64 Ls); CB 8 j8; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition pstr_seg1_post (sp gp tp s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra s0 s1 s2 s3 s4 s5 s6 s8 : word)
    (nm : bool) (S LK lh1 lh2 Ls lo : Z) (LBall : list block) (L : @clist bptr) (pl pb : bptr) (B items : Z) (bks : list (list pnode)) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j8 : list byte) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0xf0cb0) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 S) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (t_of nm lh1 lh2)) (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 Ls) (Z_to_bv 64 0) (Z_to_bv 64 1) s7 (Z_to_bv 64 (pidx_off nm)) s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xf0cfc) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (LK + 4, LK + 8); (t_of nm lh1 lh2 + 96, t_of nm lh1 lh2 + 100)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells usegs m' (bv_unsigned sp + -96) (pstr_frame Ls j8 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells usegs m' LK (mutex_cells z64 (Z_to_bv 64 16))
    /\ plh_rep m' LBall L (t_of nm lh1 lh2) pl pb B items bks.

Lemma pstr_seg1_true : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (s : PState) (LBall : list block) (L : @clist bptr) (C S LK lh1 lh2 ni vi Q1 Q2 Ls lo : Z) (str : list byte)
    (ps pk pl pb : bptr) (B items : Z) (bks : list (list pnode)),
  a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 (nmz true) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 Ls ->
  0x10000 <= C -> C + 176 <= 0x353000 -> rw_cells usegs m (C + 168) [C8 (Z_to_bv 64 S)] ->
  RHEAP s LBall m ->
  In (ps, S, 48) LBall -> rw_cells usegs m S (psd_cells LK lh1 lh2 ni vi Q1 Q2) ->
  In (pk, LK, 40) LBall -> rw_cells usegs m LK (mutex_cells z64 z64) -> ps <> pk ->
  plh_rep m LBall L (t_of true lh1 lh2) pl pb B items bks -> ~ plh_T pl pb bks ps -> ~ plh_T pl pb bks pk ->
  0x10000 <= Ls -> Ls + Z.of_nat (length str) + 1 <= 0x353000 -> bytes_at usegs m Ls (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] ->
  Z.of_nat (length str) < 2 ^ 40 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 224 -> mem_inv usegs m -> C mod 8 = 0 -> bv_unsigned sp mod 16 = 0 ->
  evt usegs (pstr_seg1_post sp gp tp s7 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 s8 true S LK lh1 lh2 Ls lo LBall L pl pb B items bks m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until bks. intros -> -> -> -> CI1 CI2 CC HP INS SCS INK LKC NSK REP NTS NTK LI1 LI2 STR NONUL NE LEN HASHES ST CLO SLO MI CAL SP16.
  cbn [nmz t_of pidx_off] in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia). assert (CLO2 : 0x353000 <= lo) by (unfold ceil_window in *; lia).
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof REP as (OL & RL & _).
  destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (INL & INB & INN).
  pose proof (RHEAP_block_range_proof _ _ _ _ HP INS) as RS. pose proof (RHEAP_block_range_proof _ _ _ _ HP INK) as RK. pose proof (RHEAP_block_range_proof _ _ _ _ HP INL) as RLH.
  unfold blk_addr, blk_size in RS, RK, RLH. cbn [fst snd] in RS, RK, RLH. destruct RS as (S0 & SAL & _ & SC48 & SIMG). destruct RK as (LK0 & LKAL & _ & LKC40 & LKIMG). destruct RLH as (_ & _ & _ & _ & LHIMG).
  assert (SAL8 : S mod 8 = 0) by (clear - SAL; Z.div_mod_to_equations; lia).
  assert (APSK : S + 48 <= LK \/ LK + 40 <= S) by (eapply (own_apart _ _ _ ps S 48 pk LK 40 HP INS INK); exact NSK).
  assert (APSL : S + 48 <= lh1 \/ lh1 + 104 <= S) by (eapply (own_apart _ _ _ ps S 48 pl lh1 104 HP INS INL); intros E; apply NTS; left; exact E).
  assert (APKL : LK + 40 <= lh1 \/ lh1 + 104 <= LK) by (eapply (own_apart _ _ _ pk LK 40 pl lh1 104 HP INK INL); intros E; apply NTK; left; exact E).
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (LK + 4, LK + 8); (lh1 + 96, lh1 + 100)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold psd_cells in SCS. unfold mutex_cells in LKC.
  (* [comment removed for export] *)
  pose proof REP as (_ & _ & (x40 & x48 & err & pad & SC) & _). unfold lh_cells, PROP_FNS, PROP_GEO, lf_comp, lf_hash, lf_hashw, lf_compw, MallocRep.wz in SC. cbn [g_nn g_na g_p g_pmax g_items] in SC.
  assert (REPAT : forall mc (x40' x48' err' pad' : word), munch [(bv_unsigned sp - 224, bv_unsigned sp); (LK + 4, LK + 8); (lh1 + 96, lh1 + 100)]%Z m mc -> wmono usegs m mc ->
    rw_cells usegs mc lh1 [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 985744); C8 (Z_to_bv 64 985692); C8 (Z_to_bv 64 987044); C8 (Z_to_bv 64 987076); C8 x40'; C8 x48';
                           C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 items); C4 err'; C4 pad'] ->
    plh_rep mc LBall L lh1 pl pb B items bks).
  { intros mc x40' x48' err' pad' MUc WMc SCc. eapply (plh_rep_after s m _ m mc); [exact HP| exact REP| exact INK| exact NTK| exact MUc| exact WMc| | exact SCc]. intros a Ha H1 H2. cbn [outside]. lia. }
  (* [comment removed for export] *)
  zstep. th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 10 ths. do 5 zstep. zstep.
  calle (eapply (get_data3_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C lo)); try lia.
  (* [comment removed for export] *)
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  zstep. zstep. zstep. th_if_lit. zstep. ubs_if. zstep. zstep.
  zstep. ths. zstep. first [ubs_if | th_if_lit]. zstep. zstep.
  calle (eapply (T_read_lock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo)); try lia.
  lazymatch goal with H : rw_cells usegs _ LK _ |- _ => unfold mutex_cells in H; rename H into LKC1 end.
  (* [comment removed for export] *)
  zstep. th_if_lit. zstep. zstep. zstep.
  lazymatch goal with FRh : rw_cells usegs ?mc (bv_unsigned sp + -96) (C8 (Z_to_bv 64 Ls) :: ?rest) |- _ =>
    apply (proj1 (rw_cells_app usegs mc _ [C8 (Z_to_bv 64 Ls)] rest)) in FRh; destruct FRh as [KEYC FRh]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRh end.
  lazymatch goal with MUh : munch _ m ?mc, WMh : wmono usegs m ?mc', SCh : rw_cells usegs ?mc'' lh1 _ |- _ => pose proof (REPAT mc _ _ _ _ MUh WMh SCh) as REP1 end.
  calle (eapply (plh_retrieve_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s LBall L lh1 pl pb B items bks (bv_unsigned sp + -96) Ls lo str m));
    try (unfold LHR_STACK, GETRN_STACK; lia).
  clear REP1. lazymatch goal with H : plh_rep ?mc LBall L lh1 pl pb B items bks |- _ => rename H into REP2; pose proof REP2 as (_ & _ & (x40b & x48b & errb & padb & SC2) & _);
     unfold lh_cells, PROP_FNS, PROP_GEO, lf_comp, lf_hash, lf_hashw, lf_compw, MallocRep.wz in SC2; cbn [g_nn g_na g_p g_pmax g_items] in SC2 end.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  calle (eapply (T_unlock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo)); try lia.
  lazymatch goal with H : rw_cells usegs _ LK _ |- _ => unfold mutex_cells in H; rename H into LKC2 end.
  (* [comment removed for export] *)
  zstep. th_if_lit. zstep. th_if_lit. zstep. zstep.
  calle (eapply (T_write_lock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo)); try lia.
  lazymatch goal with H : rw_cells usegs _ LK _ |- _ => unfold mutex_cells in H; rename H into LKC3 end.
  (* [comment removed for export] *)
  zstep. th_if_lit. zstep. th_if_lit. zstep. zstep.
  zstep. zstep. zstep.
  clear REP2. lazymatch goal with MUh : munch _ m ?mc, WMh : wmono usegs m ?mc', SCh : rw_cells usegs ?mc'' lh1 _ |- _ => pose proof (REPAT mc _ _ _ _ MUh WMh SCh) as REP3 end.
  calle (eapply (plh_retrieve_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s LBall L lh1 pl pb B items bks (bv_unsigned sp + -96) Ls lo str m));
    try (unfold LHR_STACK, GETRN_STACK; lia).
  clear REP3. lazymatch goal with H : plh_rep ?mc LBall L lh1 pl pb B items bks |- _ => rename H into REP4 end.
  (* [comment removed for export] *)
  zstep. zstep. th_if_lit.
  lazymatch goal with K1 : rw_cells usegs ?mc (bv_unsigned sp + -96) [C8 (Z_to_bv 64 Ls)], F2 : rw_cells usegs ?mc' (bv_unsigned sp + -96 + Z.of_nat 8) ?rest |- _ =>
    assert (FRJ : rw_cells usegs mc (bv_unsigned sp + -96) (C8 (Z_to_bv 64 Ls) :: rest)) by (apply (rw_cells_app usegs mc _ [C8 (Z_to_bv 64 Ls)] rest); split; [exact K1| exact F2]);
    clear K1 F2 end.
  apply evt_done. unfold pstr_seg1_post, pstr_frame. cbn [nmz t_of pidx_off]. do 14 eexists. eexists. eexists.
  split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try eassumption.
Qed.

Lemma pstr_seg1_false : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (s : PState) (LBall : list block) (L : @clist bptr) (C S LK lh1 lh2 ni vi Q1 Q2 Ls lo : Z) (str : list byte)
    (ps pk pl pb : bptr) (B items : Z) (bks : list (list pnode)),
  a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 (nmz false) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 Ls ->
  0x10000 <= C -> C + 176 <= 0x353000 -> rw_cells usegs m (C + 168) [C8 (Z_to_bv 64 S)] ->
  RHEAP s LBall m ->
  In (ps, S, 48) LBall -> rw_cells usegs m S (psd_cells LK lh1 lh2 ni vi Q1 Q2) ->
  In (pk, LK, 40) LBall -> rw_cells usegs m LK (mutex_cells z64 z64) -> ps <> pk ->
  plh_rep m LBall L (t_of false lh1 lh2) pl pb B items bks -> ~ plh_T pl pb bks ps -> ~ plh_T pl pb bks pk ->
  0x10000 <= Ls -> Ls + Z.of_nat (length str) + 1 <= 0x353000 -> bytes_at usegs m Ls (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] ->
  Z.of_nat (length str) < 2 ^ 40 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 224 -> mem_inv usegs m -> C mod 8 = 0 -> bv_unsigned sp mod 16 = 0 ->
  evt usegs (pstr_seg1_post sp gp tp s7 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 s8 false S LK lh1 lh2 Ls lo LBall L pl pb B items bks m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until bks. intros -> -> -> -> CI1 CI2 CC HP INS SCS INK LKC NSK REP NTS NTK LI1 LI2 STR NONUL NE LEN HASHES ST CLO SLO MI CAL SP16.
  cbn [nmz t_of pidx_off] in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia). assert (CLO2 : 0x353000 <= lo) by (unfold ceil_window in *; lia).
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof REP as (OL & RL & _).
  destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (INL & INB & INN).
  pose proof (RHEAP_block_range_proof _ _ _ _ HP INS) as RS. pose proof (RHEAP_block_range_proof _ _ _ _ HP INK) as RK. pose proof (RHEAP_block_range_proof _ _ _ _ HP INL) as RLH.
  unfold blk_addr, blk_size in RS, RK, RLH. cbn [fst snd] in RS, RK, RLH. destruct RS as (S0 & SAL & _ & SC48 & SIMG). destruct RK as (LK0 & LKAL & _ & LKC40 & LKIMG). destruct RLH as (_ & _ & _ & _ & LHIMG).
  assert (SAL8 : S mod 8 = 0) by (clear - SAL; Z.div_mod_to_equations; lia).
  assert (APSK : S + 48 <= LK \/ LK + 40 <= S) by (eapply (own_apart _ _ _ ps S 48 pk LK 40 HP INS INK); exact NSK).
  assert (APSL : S + 48 <= lh2 \/ lh2 + 104 <= S) by (eapply (own_apart _ _ _ ps S 48 pl lh2 104 HP INS INL); intros E; apply NTS; left; exact E).
  assert (APKL : LK + 40 <= lh2 \/ lh2 + 104 <= LK) by (eapply (own_apart _ _ _ pk LK 40 pl lh2 104 HP INK INL); intros E; apply NTK; left; exact E).
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (LK + 4, LK + 8); (lh2 + 96, lh2 + 100)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold psd_cells in SCS. unfold mutex_cells in LKC.
  (* [comment removed for export] *)
  pose proof REP as (_ & _ & (x40 & x48 & err & pad & SC) & _). unfold lh_cells, PROP_FNS, PROP_GEO, lf_comp, lf_hash, lf_hashw, lf_compw, MallocRep.wz in SC. cbn [g_nn g_na g_p g_pmax g_items] in SC.
  assert (REPAT : forall mc (x40' x48' err' pad' : word), munch [(bv_unsigned sp - 224, bv_unsigned sp); (LK + 4, LK + 8); (lh2 + 96, lh2 + 100)]%Z m mc -> wmono usegs m mc ->
    rw_cells usegs mc lh2 [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 985744); C8 (Z_to_bv 64 985692); C8 (Z_to_bv 64 987044); C8 (Z_to_bv 64 987076); C8 x40'; C8 x48';
                           C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 items); C4 err'; C4 pad'] ->
    plh_rep mc LBall L lh2 pl pb B items bks).
  { intros mc x40' x48' err' pad' MUc WMc SCc. eapply (plh_rep_after s m _ m mc); [exact HP| exact REP| exact INK| exact NTK| exact MUc| exact WMc| | exact SCc]. intros a Ha H1 H2. cbn [outside]. lia. }
  (* [comment removed for export] *)
  zstep. th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 10 ths. do 5 zstep. zstep.
  calle (eapply (get_data3_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C lo)); try lia.
  (* [comment removed for export] *)
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  zstep. zstep. zstep. th_if_lit. zstep. ubs_if. zstep.
  zstep. ths. zstep. first [ubs_if | th_if_lit]. zstep. zstep.
  calle (eapply (T_read_lock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo)); try lia.
  lazymatch goal with H : rw_cells usegs _ LK _ |- _ => unfold mutex_cells in H; rename H into LKC1 end.
  (* [comment removed for export] *)
  zstep. th_if_lit. zstep. zstep. zstep.
  lazymatch goal with FRh : rw_cells usegs ?mc (bv_unsigned sp + -96) (C8 (Z_to_bv 64 Ls) :: ?rest) |- _ =>
    apply (proj1 (rw_cells_app usegs mc _ [C8 (Z_to_bv 64 Ls)] rest)) in FRh; destruct FRh as [KEYC FRh]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRh end.
  lazymatch goal with MUh : munch _ m ?mc, WMh : wmono usegs m ?mc', SCh : rw_cells usegs ?mc'' lh2 _ |- _ => pose proof (REPAT mc _ _ _ _ MUh WMh SCh) as REP1 end.
  calle (eapply (plh_retrieve_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s LBall L lh2 pl pb B items bks (bv_unsigned sp + -96) Ls lo str m));
    try (unfold LHR_STACK, GETRN_STACK; lia).
  clear REP1. lazymatch goal with H : plh_rep ?mc LBall L lh2 pl pb B items bks |- _ => rename H into REP2; pose proof REP2 as (_ & _ & (x40b & x48b & errb & padb & SC2) & _);
     unfold lh_cells, PROP_FNS, PROP_GEO, lf_comp, lf_hash, lf_hashw, lf_compw, MallocRep.wz in SC2; cbn [g_nn g_na g_p g_pmax g_items] in SC2 end.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  calle (eapply (T_unlock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo)); try lia.
  lazymatch goal with H : rw_cells usegs _ LK _ |- _ => unfold mutex_cells in H; rename H into LKC2 end.
  (* [comment removed for export] *)
  zstep. th_if_lit. zstep. th_if_lit. zstep. zstep.
  calle (eapply (T_write_lock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo)); try lia.
  lazymatch goal with H : rw_cells usegs _ LK _ |- _ => unfold mutex_cells in H; rename H into LKC3 end.
  (* [comment removed for export] *)
  zstep. th_if_lit. zstep. th_if_lit. zstep.
  zstep. zstep. zstep.
  clear REP2. lazymatch goal with MUh : munch _ m ?mc, WMh : wmono usegs m ?mc', SCh : rw_cells usegs ?mc'' lh2 _ |- _ => pose proof (REPAT mc _ _ _ _ MUh WMh SCh) as REP3 end.
  calle (eapply (plh_retrieve_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s LBall L lh2 pl pb B items bks (bv_unsigned sp + -96) Ls lo str m));
    try (unfold LHR_STACK, GETRN_STACK; lia).
  clear REP3. lazymatch goal with H : plh_rep ?mc LBall L lh2 pl pb B items bks |- _ => rename H into REP4 end.
  (* [comment removed for export] *)
  zstep. zstep. th_if_lit.
  lazymatch goal with K1 : rw_cells usegs ?mc (bv_unsigned sp + -96) [C8 (Z_to_bv 64 Ls)], F2 : rw_cells usegs ?mc' (bv_unsigned sp + -96 + Z.of_nat 8) ?rest |- _ =>
    assert (FRJ : rw_cells usegs mc (bv_unsigned sp + -96) (C8 (Z_to_bv 64 Ls) :: rest)) by (apply (rw_cells_app usegs mc _ [C8 (Z_to_bv 64 Ls)] rest); split; [exact K1| exact F2]);
    clear K1 F2 end.
  apply evt_done. unfold pstr_seg1_post, pstr_frame. cbn [nmz t_of pidx_off]. do 14 eexists. eexists. eexists.
  split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try eassumption.
Qed.
End WithCeiling1.
