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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I1_defs Fz_I1_rep. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_I2_ppi. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_K_hash Fz_K_rep Fz_K_insert Fz_K_pstr1.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_LH_ERROR : Z := 0xea46c.

(* [comment removed for export] *)
Lemma lh_error_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lh lo : Z) (cs : list cell) (e : Z) (pad : word),
  a0 = Z_to_bv 64 lh -> 0 < lh -> rw_cells usegs m lh (cs ++ [C4 (Z_to_bv 64 e); C4 pad]) -> cells_size cs = 96%nat -> lh mod 8 = 0 -> 0 <= e < 2 ^ 31 ->
  lh + 104 <= lo ->
  stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (m' : mem),
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_LH_ERROR) fc None m (seg_rom usegs)).
Proof.
  intros until pad. intros -> LH0 SC CS LH8 ER LHLO ST LO0 LO MI. unfold FZ_LH_ERROR.
  pose proof (rw_cells_bound _ _ _ _ SC) as SB. rewrite cells_size_app in SB. rewrite CS in SB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SB.
  apply (proj1 (rw_cells_app usegs m lh cs _)) in SC. destruct SC as [_ EC]. rewrite CS in EC. replace (lh + Z.of_nat 96) with (lh + 96) in EC by lia.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_frame 16%nat [8; 8]%nat ST. do 3 ths.
  zstep. ubs_if. zstep. zstep. ubs_if.
  zstep. rewrite (t_sx32_small e) by lia.
  do 2 ths. zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release FRh (bv_unsigned sp) end.
  zstep. finish.
Qed.

(* [comment removed for export] *)
Definition pstr_seg3_post (sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra0 s0e s1e s2e s3e s4e s5e s6e s7e s8e : word)
    (lh : Z) (pl pb : bptr) (B items : Z) (bks : list (list pnode)) (h : Z) (pk : bptr) (LK idx : Z)
    (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (m : mem) (lo Bd : Z)
    : nat -> @clist bptr -> PState -> machine_state -> Prop :=
  fun f' L' s' ms' => exists (pnn : bptr) (N : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom usegs)
    /\ (f - 1 <= f')%nat /\ L' = (pnn, 24) :: L /\ cgrow L L' (wA 24) (wB 24) (wBig 24)
    /\ cstate s' ((pnn, N, 24) :: LBall) LB L' m' sp tp lo Bd
    /\ cframe (fun q => q = pk \/ plh_T pl pb bks q) [] (bv_unsigned sp - 96) s LBall L m s' ((pnn, N, 24) :: LBall) L' m'
    /\ rblock_range N 24
    /\ plh_rep m' ((pnn, N, 24) :: LBall) L' lh pl pb B (items + 1) (lupd (Z.to_nat (h mod 8)) (nth (Z.to_nat (h mod 8)) bks [] ++ [((pnn, N), h)]) bks)
    /\ rw_cells usegs m' LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)).

Lemma pstr_seg3 : crypto_malloc_stmt ->
  forall (sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra0 s0e s1e s2e s3e s4e s5e s6e s7e s8e : word) (j8 : list byte)
         (y0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 y3 y6 y7 y8 : word) (r : Z)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z)
         (S LK lh1 lh2 ni vi Q1 Q2 lh Ls An idx : Z) (str : list byte) (ps pk pn pl pb : bptr) (B items : Z) (bks : list (list pnode)),
  (1 <= f)%nat -> croom L (wA 24) (wB 24) (wBig 24) ->
  cstate s LBall LB L m (Z_to_bv 64 (bv_unsigned sp + -96)) tp lo Bd -> 96 <= bv_unsigned sp -> bv_unsigned sp <= Bd -> lo <= bv_unsigned sp - 96 - PLHI_STACK -> bv_unsigned sp mod 16 = 0 ->
  rw_cells usegs m (bv_unsigned sp + -96) (pstr_frame Ls j8 s8e s7e s6e s5e s4e s3e s2e s1e s0e ra0) ->
  In (ps, S, 48) LBall -> rw_cells usegs m S (psd_cells LK lh1 lh2 ni vi Q1 Q2) ->
  In (pk, LK, 40) LBall -> rw_cells usegs m LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 16)) ->
  plh_rep m LBall L lh pl pb B items bks -> items < 16 ->
  In (pn, An, Z.of_nat (length str) + 16) LBall -> rw_cells usegs m An [C8 (Z_to_bv 64 (An + 12)); C4 (Z_to_bv 64 idx); CB (Datatypes.S (length str)) (str ++ [Z_to_bv 8 0])] ->
  ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 20 -> 0 <= idx < 2 ^ 31 -> 0 < r < 2 ^ 31 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  ~ plh_T pl pb bks ps -> ~ plh_T pl pb bks pk -> ~ plh_T pl pb bks pn -> ps <> pk -> pn <> ps -> pn <> pk ->
  climpl f L s
    (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 S) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 lh) y3 (Z_to_bv 64 Ls) (Z_to_bv 64 An) y6 y7 y8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xf0d9c) fc None m (seg_rom usegs))
    (pstr_seg3_post sp gp tp s9 s10 s11 F fc ra0 s0e s1e s2e s3e s4e s5e s6e s7e s8e lh pl pb B items bks (lh_strhash str) pk LK idx s LBall LB L f m lo Bd).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM. intros until bks. intros Hf ROOM CST SP96 SPBD SLO SP16 FR INS SCS INK LKC REP IT16 INN NC NONUL NE LEN IDX RR HASHES NTS NTK NTN NSK NNS NNK.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold PLHI_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. rewrite unsigned_lit in ST, SPB by lia.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  set (len := Z.of_nat (length str)) in *.
  pose proof (RHEAP_block_range_proof _ _ _ _ HP INS) as RS. pose proof (RHEAP_block_range_proof _ _ _ _ HP INK) as RK. pose proof (RHEAP_block_range_proof _ _ _ _ HP INN) as RN.
  unfold blk_addr, blk_size in RS, RK, RN. cbn [fst snd] in RS, RK, RN.
  destruct RS as (S0 & _ & _ & SC48 & SIMG). destruct RK as (LK0 & LKAL & _ & LKC40 & LKIMG). destruct RN as (An0 & An16 & _ & AnC & AnIMG).
  assert (An8 : An mod 8 = 0) by (clear - An16; Z.div_mod_to_equations; lia).
  pose proof REP as (OL & RL & _). destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (INL & INB & INNS).
  pose proof (RHEAP_block_range_proof _ _ _ _ HP INL) as RLH. unfold blk_addr, blk_size in RLH. cbn [fst snd] in RLH. destruct RLH as (_ & LH16 & _).
  assert (LH8 : lh mod 8 = 0) by (clear - LH16; Z.div_mod_to_equations; lia).
  assert (APKL : LK + 40 <= lh \/ lh + 104 <= LK) by (eapply (own_apart _ _ _ pk LK 40 pl lh 104 HP INK INL); intros E; apply NTK; left; exact E).
  assert (APSK : S + 48 <= LK \/ LK + 40 <= S) by (eapply (own_apart _ _ _ ps S 48 pk LK 40 HP INS INK); exact NSK).
  assert (APNK : An + (len + 16) <= LK \/ LK + 40 <= An) by (eapply (own_apart _ _ _ pn An (len + 16) pk LK 40 HP INN INK); exact NNK).
  unfold psd_cells in SCS. unfold mutex_cells in LKC. unfold pstr_frame in FR.
  change [C8 (Z_to_bv 64 (An + 12)); C4 (Z_to_bv 64 idx); CB (Datatypes.S (length str)) (str ++ [Z_to_bv 8 0])] with ([C8 (Z_to_bv 64 (An + 12))] ++ [C4 (Z_to_bv 64 idx); CB (Datatypes.S (length str)) (str ++ [Z_to_bv 8 0])]) in NC.
  apply (proj1 (rw_cells_app usegs m An _ _)) in NC. destruct NC as [NC0 NC]. apply (proj1 (rw_cells_app usegs m _ [C4 (Z_to_bv 64 idx)] _)) in NC. destruct NC as [NC8 NC12].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in NC8, NC12. replace (An + 8 + 4) with (An + 12) in NC12 by lia.
  pose proof (proj1 (u8arr_of_rw_cells usegs _ _ _ _ NC12)) as STRN.
  pose proof (munch_refl [(bv_unsigned sp - 96 - 8416, bv_unsigned sp - 96)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite (proj2 (Z.ltb_lt 0 r)) by lia. rewrite (proj2 (Z.ltb_lt r _)) by lia. discriminate. }
  step. step. step. chere.
  eapply climpl_seq.
  { eapply (plh_insert_spec CM) with (pdb := pn) (Db := An) (ndb := len + 16) (d := An) (S := An + 12) (lo := lo) (Bd := Bd);
      [exact Hf| exact ROOM| exact CST| rewrite unsigned_lit by lia; unfold PLHI_STACK, CM_STACK, RMALLOC_STACK; lia| exact REP| exact IT16| exact INN| exact NTN| | | |
      | exact NC0| exact STRN| exact NONUL| exact NE| | exact HASHES| reflexivity| reflexivity| rewrite unsigned_lit by lia; clear - SP16; Z.div_mod_to_equations; lia| exact An8]; subst len; lia. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pnn & N & -> & -> & -> & RNG & REP1 & (x40 & x48 & pad & SC1))).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia).
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk, LK, 40) CFR1 LKC INK NTK ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as LKC1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR1 SCS INS NTS ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as SCS1.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pn, An, len + 16) CFR1 NC8 INN NTN ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as NC81.
  clear FR LKC SCS NC0 NC8 NC12 STRN.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (N0 & _ & _ & NC24 & NIMG).
  unfold lh_cells, PROP_FNS, PROP_GEO, lf_comp, lf_hash, lf_hashw, lf_compw, MallocRep.wz in SC1. cbn [g_nn g_na g_p g_pmax g_items] in SC1.
  pose proof (munch_refl [(bv_unsigned sp - 96 - 112, bv_unsigned sp - 96); (LK + 4, LK + 8)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. step.
  calle (eapply (lh_error_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lh lo
     [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 985744); C8 (Z_to_bv 64 985692); C8 (Z_to_bv 64 987044); C8 (Z_to_bv 64 987076); C8 x40; C8 x48;
      C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 (items + 1))] 0 pad)); try lia.
  (* [comment removed for export] *)
  step. th_if_lit. step. step.
  calle (eapply (T_unlock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo)); try lia.
  lazymatch goal with H : rw_cells usegs _ LK _ |- _ => unfold mutex_cells in H; rename H into LKC2 end.
  lazymatch goal with H : rw_cells usegs _ (An + Z.of_nat 8) _ |- _ => replace (An + Z.of_nat 8) with (An + 8) in H by lia end.
  step. step. ubs_if.
  step. rewrite (t_sx32_small idx) by lia.
  do 10 step.
  lazymatch goal with FRh : rw_cells usegs ?mc (bv_unsigned sp + -96) _, STh : stk usegs ?mc' lo _ |- _ => release_frame FRh STh (bv_unsigned sp) end.
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk usegs mf _ _ |- _ => rename H into STf end. lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  chere. apply climpl_done. unfold pstr_seg3_post.
  exists pnn, N. do 14 eexists. exists mf.
  split; [reflexivity|]. split; [exact FU1|]. split; [reflexivity|]. split; [exact GR1|].
  assert (INK1 : In (pk, LK, 40) ((pnn, N, 24) :: LBall)) by (right; exact INK).
  split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ _ tp lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| lia| | exact STf| lia].
    - constructor; [apply cwin_stack; lia| constructor; [| constructor]]. apply (cwin_block _ _ _ (pk, LK, 40)); [exact INK1| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - LKIMG LK0 SPR GLO SLO. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [apply cframe_refl| exact FRM1| lia| intros a X; exact X| intros q _ X Y; apply X; right; exact Y]| exact MU1| exact WM1| exact HP1| lia|].
    constructor; [apply cseg_ok_stack; lia| constructor; [| constructor]].
    apply (cseg_ok_block _ _ _ _ _ (pk, LK, 40)); [exact INK1| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
    intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. left. reflexivity. }
  split; [exact RNG|].
  split. { pose proof REP as (_ & _ & _ & _ & _ & LEN16 & _). assert (LI : (Z.to_nat (lh_strhash str mod 8) < length bks)%nat) by (pose proof (Z.mod_pos_bound (lh_strhash str) 8 ltac:(lia)); lia).
    assert (PM : Permutation (concat (lupd (Z.to_nat (lh_strhash str mod 8)) (nth (Z.to_nat (lh_strhash str mod 8)) bks [] ++ [(pnn, N, lh_strhash str)]) bks)) ((pnn, N, lh_strhash str) :: concat bks)).
    { eapply Permutation_trans; [apply concat_lupd; exact LI|].
      eapply Permutation_trans; [| apply perm_skip; apply Permutation_sym; apply (concat_split_perm bks _ LI)].
      rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_cons_app. apply Permutation_refl. }
    destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. cbn [map blk_id fst] in ND1. inversion ND1 as [|xx ll NI1 _]; subst xx ll.
    eapply (plh_rep_blockw st1 m1 _ m1 mf); [exact HP1| exact REP1| exact INK1| | exact MU1| exact WM1|].
    - intros [E|[E|E]]; [exact (NTK (or_introl E))| exact (NTK (or_intror (or_introl E)))|].
      apply in_map_iff in E. destruct E as (pa & E1 & E). apply in_map_iff in E. destruct E as (n & E2 & E).
      apply (Permutation_in _ PM) in E. destruct E as [E|E].
      + subst n. cbn [fst] in E2. subst pa. cbn in E1. apply NI1. rewrite E1. unfold blk_id. apply in_map_iff. exists (pk, LK, 40). split; [reflexivity| exact INK].
      + apply NTK. right; right. apply in_map_iff. exists pa. split; [exact E1|]. apply in_map_iff. exists n. auto.
    - intros a Ha Hn. cbn [outside]. clear - Ha Hn LO SLO. lia. }
  unfold mutex_cells. exact LKC2.
Qed.
End WithCeiling0.
