(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Stdio_iface Fz_iface Driver_iface Drv_kit Fz_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma bytes_at_same : forall m A (bs bs' : list byte),
  bytes_at usegs m A bs -> bytes_at usegs m A bs' -> length bs = length bs' -> bs = bs'.
Proof.
  intros m A bs bs' (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity.
Qed.

Lemma ssp_canary_eq : forall s LB m c, RHEAP s LB m -> ssp_cells m c -> c = rr_guard.
Proof.
  intros s LB m c HR [_ H2]. pose proof (RHEAP_ssp _ _ _ HR) as [_ G2].
  destruct H2 as [[_ B2] _]. destruct G2 as [[_ C2] _]. cbn [cells_bytes cbytes app] in B2, C2. rewrite app_nil_r in B2, C2.
  pose proof (bytes_at_same _ _ _ _ B2 C2 ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 c), <- (le_bytes_to_word_le8 rr_guard), E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cstate_init : forall s LB m sp tp lo B flags errv,
  RHEAP s LB m -> lx_statics m -> lx_flags m flags -> rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = wz RATP -> mem_inv usegs m ->
  cstate s LB LB [] m sp tp lo B.
Proof.
  intros s LB m sp tp lo B flags errv HP LXS FL AV SPB ST LO GLO ERR TP MI.
  split; [exact HP|]. split. { exists []. split; [apply Permutation_refl| reflexivity]. }
  split. { exists errv. unfold cenv. repeat match goal with |- _ /\ _ => split end; assumption. }
  split; [exact LXS|]. split; [exact FL|]. split; [| exact GLO]. destruct LXS as (_ & _ & _ & _ & _ & _ & CI). exact CI.
Qed.

(* [comment removed for export] *)
Lemma init_exit : forall (T : bptr -> Prop) W s LB m s' LBall' L' m' sp tp lo B canary,
  cstate s' LBall' LB L' m' sp tp lo B -> cframe T W (bv_unsigned sp) s LB [] m s' LBall' L' m' ->
  (forall a, rin_ivs W a -> rin_ivs LXW_CLIENT a) -> (forall b, In b LB -> ~ T (blk_id b)) ->
  RHEAP s LB m -> stderr_wfile m -> ssp_cells m canary -> B < 2 ^ 63 ->
  (cntA L' + CL_ROOM_A <= CAP_A /\ cntB L' + CL_ROOM_B <= CAP_B /\ bigsum L' + CL_ROOM_BIG <= BIG_ROOM) ->
  exists CLB errv', Permutation LBall' (CLB ++ LB) /\ cl_rel CLB L'
    /\ lx_env m' s' CLB LB sp tp B lo errv' canary
    /\ lx_pres LB (bv_unsigned sp) (LXW_CLIENT ++ [LXW_STDERR]) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros T W s LB m s' LBall' L' m' sp tp lo B canary (HP' & (CLB & PERM & IDS) & (errv' & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO)
         (CFR & KP & SO & FA) HW HT HP SEW SSP HB ROOM.
  exists CLB, errv'. split; [exact PERM|]. split; [split; [exact IDS| exact ROOM]|].
  pose proof (ssp_canary_eq _ _ _ _ HP SSP) as CAN.
  split.
  { split; [exact (RHEAP_perm _ _ _ _ HP' PERM)|]. split; [exact LXS|]. split; [exact LATCH|].
    split. { eapply stderr_wfile_agree; [exact CFR| | exact SEW]. intros a Ha. right; right. unfold stderr_addr in Ha.
             split; [lia|]. split; [unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
             split; [unfold LX_FLAGS; lia|]. intros X. apply HW in X. unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY in X. cbn [rin_ivs fst snd] in X. lia. }
    split; [subst canary; exact (RHEAP_ssp _ _ _ HP')|].
    unfold cenv. repeat match goal with |- _ /\ _ => split end; assumption. }
  split; [| split; assumption].
  eapply cfr_lx_pres; [exact CFR| |].
  - intros b Hb. split; [exact Hb| exact (HT b Hb)].
  - intros a [X| ->].
    + apply HW in X. clear - X. unfold LXW_CLIENT in *. cbn [rin_ivs app] in X |- *. tauto.
    + unfold LXW_CLIENT, LXW_LIBCRYPTO, LX_FLAGS. cbn [rin_ivs app fst snd]. lia.
Qed.
End WithCeiling0.
