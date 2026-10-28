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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_rep Fz_I1_insert1 Fz_I1_load Fz_I1_errload Fz_I1_efirst Fz_I1_crypto.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex Th_once. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_once Fz_T_atomic Fz_T_sa Fz_T_lock_new Fz_I3_base Fz_I3_shelve Fz_I3_loadstr Fz_I3_ibase.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).

Definition ICF_STACK : Z := 80 + 128 + ILS_STACK.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ICF_W : list (Z * Z) := (IC_S + 32, IC_S + 48) :: (IC_S + 96, IC_S + 104) :: IB_W ++ ILS_W.

Definition icf_res (oldcb sh : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (pk1 pk2 pm psa pn pk pl pb : bptr) (LK1 LK2 MK SA P LK lh B : Z) (u' : byte) (pad top ne : word),
       v = Z_to_bv 64 1
    /\ els_res ((pb, B, 128) :: (pl, lh, 104) :: (pk, LK, 40) :: (pn, P, 128) :: (psa, SA, 32) :: (pm, MK, 72) :: (pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall)
               ((pb, 128) :: (pl, 104) :: (pk, 40) :: (pn, 128) :: (psa, 32) :: (pm, 72) :: (pk2, 40) :: (pk1, 40) :: L)
               lh pl pb 128 (mkGeo 8 16 0 8 0) (repeat [] 16) NCRYPTO pk LK (Z_to_bv 64 1) LBall' L' m'
    /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ In q [pk; pl; pb; pn; psa; pm; pk2; pk1])
    /\ In (pm, MK, 72) LBall' /\ In (psa, SA, 32) LBall' /\ In (pn, P, 128) LBall' /\ In (pk2, LK2, 40) LBall' /\ In (pk1, LK1, 40) LBall'
    /\ rblock_range MK 72 /\ rblock_range SA 32 /\ rblock_range P 128 /\ rblock_range LK1 40 /\ rblock_range LK2 40
    /\ rw_cells usegs m' LK1 (mutex_cells z64 z64) /\ rw_cells usegs m' LK2 (mutex_cells z64 z64)
    /\ rw_cells usegs m' IC_S [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' (IC_S + 28) [C4 (Z_to_bv 64 1)]
    /\ rw_cells usegs m' (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] /\ rw_cells usegs m' (IC_S + 40) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)]
    /\ rw_cells usegs m' (IC_S + 80) [C8 (Z_to_bv 64 LK1); C8 (Z_to_bv 64 LK2)] /\ rw_cells usegs m' (IC_S + 96) [C8 (Z_to_bv 64 2)]
    /\ rw_cells usegs m' 0x31d4d0 [C4 z64]
    /\ rw_cells usegs m' 0x32dea0 [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' 0x32dea4 [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' 0x32dea8 [C4 (Z_to_bv 64 2)]
    /\ rw_cells usegs m' (RATP + -96) [C8 oldcb] /\ rw_cells usegs m' (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)] /\ rw_cells usegs m' (RATP + -150) [C1 u']
    /\ rw_cells usegs m' 0x351c90 [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' 0x351c98 [C4 z64; C4 z64; C4 sh]
    /\ rw_cells usegs m' 0x351890 [C8 (Z_to_bv 64 0xe2438)] /\ rw_cells usegs m' (0x351890 + 8 * 1) [C8 (Z_to_bv 64 0x2bdf1c)]
    /\ rw_cells usegs m' (0x351890 + 8 * 2) [C8 (Z_to_bv 64 0xe3f98)] /\ rw_cells usegs m' (0x351cd0 + 8 * 2) [C8 (Z_to_bv 64 MK)]
    /\ rw_cells usegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
    /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 P))
    /\ rw_cells usegs m' P [C8 z64; CB 120 (zeros 120)]
    /\ rw_cells usegs m' ERR_ONCE_CELL (err_statics LK lh)
    (* [comment removed for export] *)
    /\ bv_unsigned ne <= 1.

Definition init_crypto_full_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z)
         (r36 r44 o80 o88 kold0 kold1 kold2 tsd sh oldcb r0 l0 h0 : word) (b0 ib u : byte),
  (8 + 3 * NCRYPTO <= f)%nat -> croom L (8 + Z.of_nat NCRYPTO) 2 (2 * (LHA_MAX + 8192)) ->
  cstate s LBall LB L m sp tp lo Bd -> lo <= bv_unsigned sp - ICF_STACK -> bv_unsigned sp mod 16 = 0 ->
  a0 = Z_to_bv 64 2 ->
  rw_cells usegs m IC_S [C1 b0] -> rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 28) [C4 kold1] ->
  rw_cells usegs m (IC_S + 32) [C4 z64] -> rw_cells usegs m (IC_S + 36) [C4 r36] -> rw_cells usegs m (IC_S + 40) [C4 z64] -> rw_cells usegs m (IC_S + 44) [C4 r44] ->
  rw_cells usegs m (IC_S + 80) [C8 o80; C8 o88] -> rw_cells usegs m (IC_S + 96) [C8 z64] ->
  rw_cells usegs m ERR_ONCE_CELL [C4 z64; C4 r0; C8 l0; C8 h0] ->
  rw_cells usegs m 0x31d4d0 [C4 kold0] ->
  rw_cells usegs m 0x32dea0 [C1 ib] -> rw_cells usegs m 0x32dea4 [C4 z64] -> rw_cells usegs m 0x32dea8 [C4 kold2] ->
  rw_cells usegs m (RATP + -96) [C8 oldcb] -> rw_cells usegs m (RATP + -88) [C8 tsd] -> (tsd = z64 \/ tsd = Z_to_bv 64 0x351cd0) -> rw_cells usegs m (RATP + -150) [C1 u] ->
  rw_cells usegs m 0x351c90 [C4 z64] -> rw_cells usegs m 0x351c98 [C4 z64; C4 z64; C4 sh] ->
  rw_cells usegs m 0x351890 [C8 z64] -> rw_cells usegs m (0x351890 + 8 * 1) [C8 z64] -> rw_cells usegs m (0x351890 + 8 * 2) [C8 z64] -> rw_cells usegs m (0x351cd0 + 8 * 2) [C8 z64] ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_INIT_CRYPTO) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun _ => False) ICF_W (8 + 3 * NCRYPTO) (8 + Z.of_nat NCRYPTO) 1 (LHA_MAX + 8192)
           (icf_res oldcb sh LBall L)).

Theorem init_crypto_full_spec : init_base_stmt -> init_load_strings_stmt -> init_crypto_full_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros IBS ILS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd
         r36 r44 o80 o88 kold0 kold1 kold2 tsd sh oldcb r0 l0 h0 b0 ib u
         Hf ROOM CST SLO SP16 -> BI STOP K1C C32 R36 C40 R44 LKC OD HC DK IC OC KC CBC TC TV USED NK KL KY0 KY1 KY2 SLOT2.
  unfold init_base_stmt in IBS. unfold init_load_strings_stmt in ILS.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  subst tp.
  unfold ICF_STACK, ILS_STACK, CRS_STACK, ELF_STACK, GLOBALS_TOP, FZ_INIT_CRYPTO, ERR_ONCE_CELL, RATP, IC_S in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  change (3333664 + 8) with 3333672 in STOP. change (3333664 + 28) with 0x32de3c in K1C. change (3333664 + 32) with 0x32de40 in C32. change (3333664 + 36) with 3333700 in R36.
  change (3333664 + 40) with 3333704 in C40. change (3333664 + 44) with 3333708 in R44. change (3333664 + 80) with 3333744 in LKC. change (3333664 + 96) with 3333760 in OD.
  destruct ROOM as (RA & RB & RC). unfold NCRYPTO in *. change (Z.of_nat 4318) with 4318 in *.
  destruct (rheap_ssp _ _ _ HP) as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU.
  pose proof T_atomic_load_proof as AL. unfold T_atomic_load_stmt in AL.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (0x32de40, 3333700); (3344744 + -96, 3344744 + -88)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MUp.
  pose proof (conj BI (conj STOP (conj K1C (conj C32 (conj R36 (conj C40 (conj R44 (conj LKC (conj OD (conj HC (conj DK (conj IC (conj OC (conj KC (conj CBC (conj TC
             (conj USED (conj NK (conj KL (conj KY0 (conj KY1 (conj KY2 (conj SLOT2 (conj GOT GU)))))))))))))))))))))))) as CELLS.
  clear BI STOP K1C C32 R36 C40 R44 LKC OD HC DK IC OC KC CBC TC USED NK KL KY0 KY1 KY2 SLOT2 GOT GU.
  (* [comment removed for export] *)
  cprefix. step. th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST. do 8 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (TR : forall A cs, rw_cells usegs m A cs -> A + Z.of_nat (cells_size cs) <= 3485696 -> rw_cells usegs mm A cs)
      by (intros A cs H HB; eapply rw_cells_transport; [exact H| exact MUp| exact WM| cbn [disjoint_from]; lia]) end.
  destruct CELLS as (BI & STOP & K1C & C32 & R36 & C40 & R44 & LKC & OD & HC & DK & IC & OC & KC & CBC & TC & USED & NK & KL & KY0 & KY1 & KY2 & SLOT2 & GOT & GU).
  apply TR in BI; [| cbn; lia]. apply TR in STOP; [| cbn; lia]. apply TR in K1C; [| cbn; lia]. apply TR in C32; [| cbn; lia]. apply TR in R36; [| cbn; lia].
  apply TR in C40; [| cbn; lia]. apply TR in R44; [| cbn; lia]. apply TR in LKC; [| cbn; lia]. apply TR in OD; [| cbn; lia]. apply TR in HC; [| cbn; lia].
  apply TR in DK; [| cbn; lia]. apply TR in IC; [| cbn; lia]. apply TR in OC; [| cbn; lia]. apply TR in KC; [| cbn; lia]. apply TR in CBC; [| cbn; lia].
  apply TR in TC; [| cbn; lia]. apply TR in USED; [| cbn; lia]. apply TR in NK; [| cbn; lia]. apply TR in KL; [| cbn; lia]. apply TR in KY0; [| cbn; lia].
  apply TR in KY1; [| cbn; lia]. apply TR in KY2; [| cbn; lia]. apply TR in SLOT2; [| cbn; lia]. apply TR in GOT; [| cbn; lia]. apply TR in GU; [| cbn; lia].
  clear TR MUp.
  do 4 step. step. step. step. th_if_lit.
  do 4 step. step.
  apply (cb8_c8_in' _ _ [CB 8 _] _ _) in FR. cbn [app] in FR.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: C8 ?tv :: ?rest) =>
    change (CB 8 j :: C8 tv :: rest) with ([CB 8 j] ++ [C8 tv] ++ rest) in FR end.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR. destruct FR as [FR0 FR]. apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR. destruct FR as [FRT FRS].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRT, FRS.
  replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in * by lia. replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) in * by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (proj1 OD : ro_cells usegs mm 3333760 [C8 (Z_to_bv 64 0)]) as ODro end.
  calle (eapply AL with (lo := lo)); try lia.
  clear AL ODro.
  step. step. th_if_lit. step. step. step. th_if_lit.
  do 3 step. step.
  pose proof T_run_once_enter_proof as OE. unfold T_run_once_enter_stmt, ssp_cells, got_ssp, ssp_guard in OE.
  tcall (OE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0xe20e0 oldcb rr_guard).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  clear OE. cbv beta delta [mkR]. try th_ret_lit. try cret_lit. chere.
  unfold ONCE_RET_INIT, RUN_ONCE_RET, once_full_cells, ONCE_UNDO, ONCE_RET_FULL in *.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mi end.
  lazymatch goal with H : rw_cells usegs mi 0x32de40 _ |- _ => rename H into CC1 end.
  lazymatch goal with H : rw_cells usegs mi (3344744 + -96) _ |- _ => rename H into CB1 end.
  lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -80 + -128) _ |- _ => rename H into OF1 end.
  lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -80 + -32) _ |- _ => rename H into OF2 end.
  lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -80 + -16) _ |- _ => rename H into OF3 end.
  lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -72) _ |- _ => rename H into TMP end.
  lazymatch goal with H : stk usegs mi _ _ |- _ => rename H into STi end.
  lazymatch goal with H : mem_inv usegs mi |- _ => rename H into MIi end.
  assert (CSTi : cstate s LBall LB L mi (Z_to_bv 64 (bv_unsigned sp + -80 + -128)) (Z_to_bv 64 3344744) lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m mi _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIi| | lia| lia| | rewrite unsigned_lit by lia; exact STi| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply cwin_bss; lia|]. apply Forall_cons; [unfold cwin; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRa : cframe (fun _ => False) ICF_W (bv_unsigned sp) s LBall L m s LBall L mi).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    repeat (apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold ICF_W, IB_W, ILS_W, SHV_W, IC_S, RATP; cbn [rin_ivs fst snd app]; lia]|]). apply Forall_nil. }
  eapply climpl_seq.
  { eapply IBS with (lo := lo) (Bd := Bd); [lia| unfold croom; unfold LHA_MAX in RC; lia| exact CSTi| rewrite unsigned_lit by lia; unfold IB_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia
      | exact BI| exact K1C| exact R36| exact LKC| exact DK| exact TC| exact TV| exact NK| exact KL| exact KY0| exact KY1]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pk1 & pk2 & LK1 & LK2 & -> & -> & RNG1 & RNG2 & MC1 & MC2 & BI1 & K1C1 & R361 & LKC1 & DK1 & TC1 & NK1 & KL1 & KY01 & KY11)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). unfold IB_W, IC_S, RATP in FRM1, TC1, R361, K1C1, LKC1, BI1.
  change (3333664 + 28) with 0x32de3c in K1C1. change (3333664 + 36) with 3333700 in R361. change (3333664 + 80) with 3333744 in LKC1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR0 ltac:(lia)) as FR01.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRS ltac:(lia)) as FRS1.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 TMP ltac:(lia)) as TMP1.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OF1 ltac:(lia)) as OF1b.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OF2 ltac:(lia)) as OF2b.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OF3 ltac:(lia)) as OF3b.
  cst_static CFR1 STOP STOP1. cst_static CFR1 CC1 CC2. cst_static CFR1 C40 C401. cst_static CFR1 R44 R441. cst_static CFR1 OD OD1. cst_static CFR1 HC HC1.
  cst_static CFR1 IC IC1. cst_static CFR1 OC OC1. cst_static CFR1 KC KC1. cst_static CFR1 CB1 CB2. cst_static CFR1 USED USED1. cst_static CFR1 KY2 KY21. cst_static CFR1 SLOT2 SLOT21.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  destruct (rheap_ssp _ _ _ HP1) as [GOT1 GU1]. unfold got_ssp, ssp_guard in GOT1, GU1.
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 NDL1].
  pose proof RNG1 as (LK1P & _ & _ & LK1C & LK1IMG). pose proof RNG2 as (LK2P & _ & _ & LK2C & LK2IMG).
  unfold mutex_cells in MC1, MC2.
  assert (FRM0 : cframe (fun _ => False) ICF_W (bv_unsigned sp) s LBall L m st1 ((pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall) ((pk2, 40) :: (pk1, 40) :: L) m1).
  { eapply cframe_call; [exact FRa| exact FRM1| lia| | intros q _ X; exact X].
    intros a X. unfold ICF_W, IB_W, ILS_W, SHV_W, IC_S, RATP. cbn [rin_ivs fst snd app] in X |- *. lia. }
  clear FRa CSTi CFR1 FRM1.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp - 80); (0x32de40, 3333700); (3333704, 3333708); (3344744 + -96, 3344744 + -88)]%Z m1) as MU1.
  pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix.
  pose proof (T_run_once_leave_proof) as OL. unfold T_run_once_leave_stmt, ssp_cells, got_ssp, ssp_guard, ONCE_RET_INIT, once_full_cells, ONCE_UNDO, ONCE_RET_FULL, RUN_ONCE_RET in OL.
  tcall (OL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -80) 0x32de40).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  clear OL. cbv beta delta [mkR]. try th_ret_lit. try cret_lit.
  step. step. th_if_lit. step. step. th_if_lit. step. step. step. th_if_lit. step. th_if_lit.
  step. step. th_if_lit. step. step. th_if_lit.
  do 3 step. step.
  pose proof T_run_once_enter_proof as OE. unfold T_run_once_enter_stmt, ssp_cells, got_ssp, ssp_guard in OE.
  tcall (OE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0xe219c oldcb rr_guard).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  clear OE. cbv beta delta [mkR]. try th_ret_lit. try cret_lit. chere.
  unfold ONCE_RET_INIT, RUN_ONCE_RET, once_full_cells, ONCE_UNDO, ONCE_RET_FULL in *.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mj end.
  lazymatch goal with H : rw_cells usegs mj 0x32de40 _ |- _ => rename H into CC3 end.
  lazymatch goal with H : rw_cells usegs mj 3333704 _ |- _ => rename H into CD3 end.
  lazymatch goal with H : rw_cells usegs mj (3344744 + -96) _ |- _ => rename H into CB3 end.
  lazymatch goal with H : rw_cells usegs mj (bv_unsigned sp + -80 + -128) _ |- _ => rename H into OF1c end.
  lazymatch goal with H : rw_cells usegs mj (bv_unsigned sp + -80 + -32) _ |- _ => rename H into OF2c end.
  lazymatch goal with H : rw_cells usegs mj (bv_unsigned sp + -80 + -16) _ |- _ => rename H into OF3c end.
  lazymatch goal with H : stk usegs mj _ _ |- _ => rename H into STj end.
  lazymatch goal with H : mem_inv usegs mj |- _ => rename H into MIj end.
  assert (ONCEj : rw_cells usegs mj 0x32de40 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)]).
  { change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] with ([C4 (Z_to_bv 64 2)] ++ [C4 (Z_to_bv 64 1)]). apply rw_cells_app. split; [exact CC3|].
    cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4. exact R361. }
  assert (CSTj : cstate st1 ((pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall) LB ((pk2, 40) :: (pk1, 40) :: L) mj (Z_to_bv 64 (bv_unsigned sp + -80 + -128)) (Z_to_bv 64 3344744) lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m1 mj _ _ _ lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIj| | lia| lia| | rewrite unsigned_lit by lia; exact STj| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply cwin_bss; lia|]. apply Forall_cons; [apply cwin_bss; lia|].
      apply Forall_cons; [unfold cwin; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRb : cframe (fun _ => False) ICF_W (bv_unsigned sp) s LBall L m st1 ((pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall) ((pk2, 40) :: (pk1, 40) :: L) mj).
  { eapply cframe_seg; [exact FRM0| exact MU1| exact WM1| exact HP1| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    repeat (apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold ICF_W, IB_W, ILS_W, SHV_W, IC_S, RATP; cbn [rin_ivs fst snd app]; lia]|]). apply Forall_nil. }
  clear FRM0.
  eapply climpl_seq.
  { eapply ILS with (lo := lo) (Bd := Bd) (r0 := r0) (l0 := l0) (h0 := h0);
      [clear - Hf FU1; lia| unfold croom, cgrow in *; lia| exact CSTj| rewrite unsigned_lit by lia; unfold ILS_STACK, CRS_STACK, ELF_STACK; lia| rewrite unsigned_lit by lia; lia
      | exact STOP1| exact ONCEj| exact R441| exact OD1| exact HC1| exact IC1| exact OC1| exact KC1| exact CB3| exact TC1| right; reflexivity| exact USED1
      | exact NK1| exact KL1| exact KY11| rewrite unsigned_lit by lia; lia| exact KY21| exact SLOT21]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & LRES).
  destruct LRES as (pm & psa & pn & MK & SA & P & u' & pad & top & ne & pk & pl & pb & LK & lh & B & ELS & FRESH & INM & INS & INP & RNGM & RNGS & RNGP
                    & IC2 & OC2 & KC2 & CB4 & TC2 & USED2 & NK2 & KL2 & KY12 & KY22 & SLOT22 & BLKM & HDR & PBLK & HCE & R442 & NEF).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia). unfold ILS_W, SHV_W, IC_S, RATP in FRM2. unfold RATP in CB4, TC2, USED2. unfold IC_S in R442. unfold ERR_ONCE_CELL, err_statics in HCE.
  change (3333664 + 44) with 3333708 in R442.
  pose proof FRM2 as (CFR2 & KP2 & _). cbn [app] in CFR2.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR01 ltac:(lia)) as FR02.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FRS1 ltac:(lia)) as FRS2.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 TMP1 ltac:(lia)) as TMP2.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OF1c ltac:(lia)) as OF1d.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OF2c ltac:(lia)) as OF2d.
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 OF3c ltac:(lia)) as OF3d.
  cst_static CFR2 STOP1 STOP2. cst_static CFR2 CC3 CC4. cst_static CFR2 R361 R362. cst_static CFR2 CD3 CD4. cst_static CFR2 OD1 OD2.
  cst_static CFR2 BI1 BI2. cst_static CFR2 K1C1 K1C2. cst_static CFR2 LKC1 LKC2. cst_static CFR2 DK1 DK2. cst_static CFR2 KY01 KY02.
  assert (INK11 : In (pk1, LK1, 40) ((pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall)) by (right; left; reflexivity).
  assert (INK21 : In (pk2, LK2, 40) ((pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall)) by (left; reflexivity).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk1, LK1, 40) CFR2 MC1 INK11 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as MC12.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk2, LK2, 40) CFR2 MC2 INK21 (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as MC22.
  assert (INK12 : In (pk1, LK1, 40) LBall2) by exact (proj1 KP2 _ INK11 (fun X => X)).
  assert (INK22 : In (pk2, LK2, 40) LBall2) by exact (proj1 KP2 _ INK21 (fun X => X)).
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by lia.
  destruct (rheap_ssp _ _ _ HP2) as [GOT2 GU2]. unfold got_ssp, ssp_guard in GOT2, GU2.
  destruct ELS as [_ ELS']. destruct ELS' as (pb' & B' & nmb' & g' & bks' & REP & IT & NM & GRL & TK & MC & INK2).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST2 INK2) as (LK0 & _ & _ & LK40 & LKIMG).
  pose proof RNGM as (M0 & _ & _ & M72 & MIMG). pose proof RNGS as (S0 & _ & _ & S32 & SIMG). pose proof RNGP as (P0 & _ & _ & P128 & PIMG).
  unfold mutex_cells in MC. unfold sa_hdr in HDR.
  pose proof T_atomic_or_proof as AO. unfold T_atomic_or_stmt in AO.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (3333704, 3333708); (3344744 + -96, 3344744 + -88); (3333760, 3333768)]%Z m2) as MU2.
  pose proof (wmono_refl usegs m2) as WM2.
  (* [comment removed for export] *)
  cprefix.
  pose proof (T_run_once_leave_proof) as OL. unfold T_run_once_leave_stmt, ssp_cells, got_ssp, ssp_guard, ONCE_RET_INIT, once_full_cells, ONCE_UNDO, ONCE_RET_FULL, RUN_ONCE_RET in OL.
  tcall (OL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -80) 3333704).
  all: try first [eassumption | reflexivity | lia | split; eassumption].
  clear OL. cbv beta delta [mkR]. try th_ret_lit. try cret_lit.
  step. step. th_if_lit. step. step. th_if_lit.
  do 10 (step; step; th_if_lit).
  step. do 3 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mk end.
  lazymatch goal with H : rw_cells usegs mk 3333760 _ |- _ => rename H into ODk end.
  lazymatch goal with H : rw_cells usegs mk (bv_unsigned sp + -72) _ |- _ => rename H into TMPk end.
  tcall (AO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (Z_to_bv 64 0) (Z_to_bv 64 0)).
  all: try first [eassumption | reflexivity | lia].
  clear AO. cbv beta delta [mkR]. try th_ret_lit. try cret_lit.
  lazymatch goal with H : ?nv = Z_to_bv 64 (Z.lor 0 2) |- _ => change (Z.lor 0 2) with 2 in H; subst nv end.
  step. step. step. do 8 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into ST3 end.
  lazymatch goal with H : rw_cells usegs mf (bv_unsigned sp + -80) _ |- _ => rename H into FR03 end.
  lazymatch goal with H : rw_cells usegs mf (bv_unsigned sp + -72) _ |- _ => rename H into TMP3 end.
  lazymatch goal with H : rw_cells usegs mf (bv_unsigned sp + -64) _ |- _ => rename H into FRS3 end.
  release_frame FR03 ST3 (bv_unsigned sp + -72). release_frame TMP3 ST3 (bv_unsigned sp + -64). release_frame FRS3 ST3 (bv_unsigned sp).
  step. step.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
  lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  lazymatch goal with H : rw_cells usegs mf LK _ |- _ => rename H into MCf end.
  lazymatch goal with H : rw_cells usegs mf LK1 _ |- _ => rename H into MC1f end.
  lazymatch goal with H : rw_cells usegs mf LK2 _ |- _ => rename H into MC2f end.
  lazymatch goal with H : rw_cells usegs mf SA _ |- _ => rename H into HDRf end.
  chere. apply climpl_done.
  exists (Z_to_bv 64 1), mf, LBall2.
  split; [unfold cret; do 14 eexists; reflexivity|].
  split; [clear - Hf FU1 FU2; lia|].
  split; [pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) as GR; clear - GR; unfold cgrow in *; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m2 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply cwin_bss; lia|]. apply Forall_cons; [unfold cwin; cbn [fst snd]; lia|].
      apply Forall_cons; [apply cwin_bss; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM2| lia| | intros q _ X; exact X]| exact MU2| exact WM2| exact HP2| lia|].
    - intros a X. unfold ICF_W, IB_W, ILS_W, SHV_W, IC_S, RATP. cbn [rin_ivs fst snd app] in X |- *. lia.
    - apply Forall_cons; [apply cseg_ok_stack; lia|].
      repeat (apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold ICF_W, IB_W, ILS_W, SHV_W, IC_S, RATP; cbn [rin_ivs fst snd app]; lia]|]). apply Forall_nil. }
  unfold icf_res. exists pk1, pk2, pm, psa, pn, pk, pl, pb, LK1, LK2, MK, SA, P, LK, lh, B, u'. do 3 eexists.
  split; [reflexivity|].
  split. { split; [reflexivity|]. exists pb', B', nmb', g', bks'.
    split. { eapply (lh_rep_seg st2 DVERR m2 mf); [exact HP2| exact REP| exact MU2| exact WM2|].
      repeat (apply Forall_cons; [left; cbn [fst snd]; intros a Ha Hc Hi; lia|]). apply Forall_nil. }
    split; [exact IT|]. split; [exact NM|]. split; [exact GRL|]. split; [exact TK|]. split; [unfold mutex_cells; exact MCf| exact INK2]. }
  split. { intros q Hq HIn.
    assert (Hq1 : In q (map blk_id ((pk2, LK2, 40) :: (pk1, LK1, 40) :: LBall)) \/ In q (map fst ((pk2, 40) :: (pk1, 40) :: L)))
      by (destruct Hq as [Hq|Hq]; [left| right]; cbn [map blk_id fst]; right; right; exact Hq).
    destruct (FRESH q Hq1) as (N1 & N2 & N3 & N4 & N5 & N6).
    cbn [map blk_id fst] in ND1, NDL1.
    inversion ND1 as [|hd tl NI2 ND1']; subst. inversion ND1' as [|hd' tl' NI1 ND1'']; subst.
    inversion NDL1 as [|hd tl NI2L NDL1']; subst. inversion NDL1' as [|hd' tl' NI1L NDL1'']; subst.
    destruct HIn as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]];
      [exact (N1 (eq_sym E))| exact (N2 (eq_sym E))| exact (N3 (eq_sym E))| exact (N4 (eq_sym E))| exact (N5 (eq_sym E))| exact (N6 (eq_sym E))| subst q| subst q].
    - destruct Hq as [Hq|Hq]; [apply NI2; right; exact Hq| apply NI2L; right; exact Hq].
    - destruct Hq as [Hq|Hq]; [exact (NI1 Hq)| exact (NI1L Hq)]. }
  split; [exact INM|]. split; [exact INS|]. split; [exact INP|]. split; [exact INK22|]. split; [exact INK12|].
  split; [exact RNGM|]. split; [exact RNGS|]. split; [exact RNGP|]. split; [exact RNG1|]. split; [exact RNG2|].
  unfold mutex_cells, sa_hdr, IC_S, RATP, ERR_ONCE_CELL, err_statics.
  change (3333664 + 28) with 0x32de3c. change (3333664 + 32) with 0x32de40. change (3333664 + 40) with 3333704. change (3333664 + 80) with 3333744. change (3333664 + 96) with 3333760.
  repeat match goal with |- _ /\ _ => split end; try eassumption.
  - change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] with ([C4 (Z_to_bv 64 2)] ++ [C4 (Z_to_bv 64 1)]). apply rw_cells_app. split; [eassumption|].
    cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4. eassumption.
  - change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] with ([C4 (Z_to_bv 64 2)] ++ [C4 (Z_to_bv 64 1)]). apply rw_cells_app. split; [eassumption|].
    cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4. eassumption.
Qed.
End WithCeiling0.
