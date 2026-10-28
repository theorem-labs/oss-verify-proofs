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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Stdio_iface Fz_iface Driver_iface Drv_kit Fz_kit Fz_cimg Fz_M_malloc Fz_M_zalloc Fz_I1_defs Fz_I1_rep Fz_I1_load Fz_I1_errload Fz_I1_efirst Fz_I1_crypto.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex Th_key Th_once. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_sa Fz_T_sk Fz_T_lock_new Fz_T_tevent Fz_T_mtl Fz_T_its Fz_I3_base Fz_I3_shelve Fz_I3_loadstr Fz_I3_ibase Fz_I3_full Fz_I3_egsi Fz_I3_eclear Fz_I3_fxi Fz_I3_glue.
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
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
Lemma in_nodup_ids : forall (l : list block) x y, List.NoDup (map blk_id l) -> In x l -> In y l -> blk_id x = blk_id y -> x = y.
Proof.
  induction l as [|b l IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn [map] in ND. inversion ND as [|b' l' NI ND']; subst.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - reflexivity.
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
  - exact (IH x y ND' Hx Hy E).
Qed.
Lemma blk_ids_ne : forall (l : list block) (p q : bptr) A n A' n', List.NoDup (map blk_id l) -> In (p, A, n) l -> In (q, A', n') l -> n <> n' -> p <> q.
Proof. intros l p q A n A' n' ND H1 H2 NE E. apply NE. pose proof (in_nodup_ids l _ _ ND H1 H2 E) as X. apply (f_equal blk_size) in X. exact X. Qed.

Lemma nodup_app_disj : forall (l1 l2 : list bptr) q, List.NoDup (l1 ++ l2) -> In q l2 -> ~ In q l1.
Proof.
  induction l1 as [|a l1 IH]; intros l2 q ND H2 H1; [exact H1|].
  cbn [app] in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct H1 as [<-|H1]; [apply NI; apply in_app_iff; right; exact H2| exact (IH l2 q ND' H2 H1)].
Qed.

Section Top.
  (* [comment removed for export] *)
  Variables (CI_EV : nat) (CI_A CI_B CI_BIG CI_STK : Z) (CI_W : list (Z * Z)).
  Variable CI_PRE : list block -> @clist bptr -> mem -> Prop.
  Variable CI_FP : Z -> Prop.
  Variable CI_RES : bptr -> list block -> @clist bptr -> mem -> Prop.
  Hypothesis CTXI : context_init_abs_stmt CI_EV CI_A CI_B CI_BIG CI_STK CI_W CI_PRE CI_RES.
  Hypothesis CI_W_RANGE : forall a, rin_ivs CI_W a -> DC_CTX <= a < DC_CTX + 328.
  (* [comment removed for export] *)
  Hypothesis CI_W_IP12 : forall a, rin_ivs CI_W a -> ~ (0x32df38 <= a < 0x32df40).
  Hypothesis CI_STK_POS : 112 <= CI_STK.
  Hypothesis CI_NUMS : 0 <= CI_A /\ 0 <= CI_B /\ 0 <= CI_BIG.
  Hypothesis CI_PRE_agree : forall LBall L m m', agree_on CI_FP m m' -> CI_PRE LBall L m -> CI_PRE LBall L m'.
  Hypothesis CI_FP_ok : forall a, CI_FP a -> 0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS /\ ~ rin_ivs (FXI_PW) a.
  Hypothesis CI_RES_cfr : forall pk LBall' L' m m' SPX, CI_RES pk LBall' L' m -> cfr (fun q => q = pk) (FXI_AW) SPX LBall' m m' -> CI_RES pk LBall' L' m'.

  (* [comment removed for export] *)
  Definition ci_site (m : mem) : Prop :=
    exists (LK1 LK2 G LKe lh : Z),
       rw_cells usegs m IC_S [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] /\ rw_cells usegs m (IC_S + 28) [C4 (Z_to_bv 64 1)]
    /\ rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] /\ rw_cells usegs m (IC_S + 40) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)]
    /\ rw_cells usegs m (IC_S + 80) [C8 (Z_to_bv 64 LK1); C8 (Z_to_bv 64 LK2)] /\ rw_cells usegs m (IC_S + 96) [C8 (Z_to_bv 64 2)]
    /\ rw_cells usegs m 0x32de90 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 G)]
    /\ rw_cells usegs m 0x32dea0 [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m 0x32dea4 [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m 0x32dea8 [C4 (Z_to_bv 64 2)]
    /\ rw_cells usegs m ERR_ONCE_CELL (err_statics LKe lh) /\ rw_cells usegs m 0x351010 [C4 z64].
  Hypothesis CI_PRE_intro : forall LBall L m, ci_site m -> CI_PRE LBall L m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition FI_EV : nat := 8 + 3 * NCRYPTO + 7 + CI_EV.
  Definition FI_W : list (Z * Z) := ICF_W ++ EGSI_W ++ GDC_W CI_W.

  (* [comment removed for export] *)
  Definition finit_res (oldcb sh : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
    fun v LBall' L' m' => v = Z_to_bv 64 1 /\
     exists (pe pm psa pn ph ptn pg psk plk pd pk1 pk2 pkx : bptr) (E MK SA P H N G SK LK D LK1 LK2 LKX LKe lh : Z) (u' : byte) (pad top ne : word),
        In (pe, E, 904) LBall' /\ In (pm, MK, 72) LBall' /\ In (psa, SA, 32) LBall' /\ In (pn, P, 128) LBall' /\ In (ph, H, 8) LBall' /\ In (ptn, N, 32) LBall'
     /\ In (pg, G, 16) LBall' /\ In (psk, SK, 56) LBall' /\ In (plk, LK, 40) LBall' /\ In (pd, D, 32) LBall'
     /\ In (pk1, LK1, 40) LBall' /\ In (pk2, LK2, 40) LBall' /\ In (pkx, LKX, 40) LBall'
     /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> ~ In q [pe; pm; psa; pn; ph; ptn; pg; psk; plk; pd; pk1; pk2; pkx])
     /\ rw_cells usegs m' E es_clean
     /\ rw_cells usegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
     /\ rw_cells usegs m' SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 P)) /\ rw_cells usegs m' P [C8 (Z_to_bv 64 E); CB 120 (zeros 120)]
     /\ rw_cells usegs m' H [C8 (Z_to_bv 64 N)] /\ rw_cells usegs m' N [C8 z64; C8 z64; C8 (Z_to_bv 64 FZ_ERR_DEL_THREAD_STATE); C8 z64]
     /\ rw_cells usegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]
     /\ rw_cells usegs m' SK (sk_cells (Z_to_bv 64 1) z64 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) z64 (Z_to_bv 64 0xe2d48) (Z_to_bv 64 0xe2d20) (Z_to_bv 64 0xe2d74))
     /\ rw_cells usegs m' LK (mutex_cells z64 z64) /\ rw_cells usegs m' D [C8 (Z_to_bv 64 H); CB 24 (zeros 24)]
     /\ rw_cells usegs m' LK1 (mutex_cells z64 z64) /\ rw_cells usegs m' LK2 (mutex_cells z64 z64) /\ rw_cells usegs m' LKX (mutex_cells z64 z64)
     /\ rw_cells usegs m' IC_S [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' (IC_S + 8) [C1 (Z_to_bv 8 0)] /\ rw_cells usegs m' (IC_S + 28) [C4 (Z_to_bv 64 1)]
     /\ rw_cells usegs m' (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] /\ rw_cells usegs m' (IC_S + 40) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)]
     /\ rw_cells usegs m' (IC_S + 80) [C8 (Z_to_bv 64 LK1); C8 (Z_to_bv 64 LK2)] /\ rw_cells usegs m' (IC_S + 96) [C8 (Z_to_bv 64 2)]
     /\ rw_cells usegs m' 0x32de90 [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 G)]
     /\ rw_cells usegs m' 0x32dea0 [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' 0x32dea4 [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' 0x32dea8 [C4 (Z_to_bv 64 2)]
     /\ rw_cells usegs m' DC_S [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' (DC_S + 4) [C4 (Z_to_bv 64 3)] /\ rw_cells usegs m' (DC_S + 8) [C4 (Z_to_bv 64 2)]
     /\ rw_cells usegs m' (DC_S + 12) [C4 (Z_to_bv 64 1)] /\ rw_cells usegs m' (DC_S + 16) [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' (DC_S + 20) [C4 (Z_to_bv 64 1)]
     /\ rw_cells usegs m' DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LKX)]
     /\ rw_cells usegs m' ERR_ONCE_CELL (err_statics LKe lh)
     /\ rw_cells usegs m' 0x31d4d0 [C4 z64] /\ rw_cells usegs m' (0x31d4d0 + 4) [C4 (Z_to_bv 64 0xffffffff)]
     /\ rw_cells usegs m' (RATP + -96) [C8 oldcb] /\ rw_cells usegs m' (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)] /\ rw_cells usegs m' (RATP + -150) [C1 u']
     /\ rw_cells usegs m' 0x351c90 [C4 (Z_to_bv 64 3)] /\ rw_cells usegs m' 0x351c98 [C4 z64; C4 z64; C4 sh]
     /\ rw_cells usegs m' 0x351890 [C8 (Z_to_bv 64 0xe2438)] /\ rw_cells usegs m' (0x351890 + 8 * 1) [C8 (Z_to_bv 64 0x2bdf1c)]
     /\ rw_cells usegs m' (0x351890 + 8 * 2) [C8 (Z_to_bv 64 0xe3f98)] /\ rw_cells usegs m' (0x351890 + 8 * 3) [C8 (Z_to_bv 64 0x2bdf1c)]
     /\ rw_cells usegs m' 0x351cd0 [C8 (Z_to_bv 64 H)] /\ rw_cells usegs m' (0x351cd0 + 8 * 2) [C8 (Z_to_bv 64 MK)] /\ rw_cells usegs m' (0x351cd0 + 8 * 3) [C8 z64]
     /\ rw_cells usegs m' 0x351010 [C4 z64]
     (* [comment removed for export] *)
     /\ bv_unsigned ne <> 0
     /\ CI_RES pkx LBall' L' m'.

  (* [comment removed for export] *)
  Definition finit_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z)
           (b0 ib u : byte) (kold0 kold1 kold2 r36 r44 o80 o88 tsd sh oldcb r0 l0 h0 er0 eg0 dkold dr12 dr20 : word),
    (FI_EV <= f)%nat -> croom L (14 + Z.of_nat NCRYPTO + CI_A) (2 + CI_B) (2 * (LHA_MAX + 8192) + CI_BIG) ->
    cstate s LBall LB L m sp tp lo Bd ->
    lo <= bv_unsigned sp - (16 + ICF_STACK) -> lo <= bv_unsigned sp - (16 + ECL_STACK) -> lo <= bv_unsigned sp - (16 + FXI_STACK CI_STK) -> bv_unsigned sp mod 16 = 0 ->
    rw_cells usegs m IC_S [C1 b0] -> rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 28) [C4 kold1] ->
    rw_cells usegs m (IC_S + 32) [C4 z64] -> rw_cells usegs m (IC_S + 36) [C4 r36] -> rw_cells usegs m (IC_S + 40) [C4 z64] -> rw_cells usegs m (IC_S + 44) [C4 r44] ->
    rw_cells usegs m (IC_S + 80) [C8 o80; C8 o88] -> rw_cells usegs m (IC_S + 96) [C8 z64] ->
    rw_cells usegs m ERR_ONCE_CELL [C4 z64; C4 r0; C8 l0; C8 h0] ->
    rw_cells usegs m 0x31d4d0 [C4 kold0] -> rw_cells usegs m (0x31d4d0 + 4) [C4 (Z_to_bv 64 0xffffffff)] ->
    rw_cells usegs m 0x32de90 [C4 z64; C4 er0; C8 eg0] ->
    rw_cells usegs m 0x32dea0 [C1 ib] -> rw_cells usegs m 0x32dea4 [C4 z64] -> rw_cells usegs m 0x32dea8 [C4 kold2] ->
    rw_cells usegs m DC_S [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (DC_S + 4) [C4 dkold] -> rw_cells usegs m (DC_S + 8) [C4 z64] -> rw_cells usegs m (DC_S + 12) [C4 dr12] ->
    rw_cells usegs m (DC_S + 16) [C4 z64] -> rw_cells usegs m (DC_S + 20) [C4 dr20] -> ctx0 m ->
    rw_cells usegs m (RATP + -96) [C8 oldcb] -> rw_cells usegs m (RATP + -88) [C8 tsd] -> (tsd = z64 \/ tsd = Z_to_bv 64 0x351cd0) -> rw_cells usegs m (RATP + -150) [C1 u] ->
    rw_cells usegs m 0x351c90 [C4 z64] -> rw_cells usegs m 0x351c98 [C4 z64; C4 z64; C4 sh] ->
    rw_cells usegs m 0x351890 [C8 z64] -> rw_cells usegs m (0x351890 + 8 * 1) [C8 z64] -> rw_cells usegs m (0x351890 + 8 * 2) [C8 z64] -> rw_cells usegs m (0x351890 + 8 * 3) [C8 z64] ->
    rw_cells usegs m 0x351cd0 [C8 z64] -> rw_cells usegs m (0x351cd0 + 8 * 2) [C8 z64] -> rw_cells usegs m (0x351cd0 + 8 * 3) [C8 z64] ->
    rw_cells usegs m 0x351010 [C4 z64] ->
    climpl f L s
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 LX_INIT) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (fun _ => False) FI_W FI_EV
             (14 + Z.of_nat NCRYPTO + CI_A) (2 + CI_B) (LHA_MAX + 8192 + (904 + 8192) + CI_BIG) (finit_res oldcb sh LBall L)).

  (* [comment removed for export] *)
  Ltac cst_staticW CFR H Hn :=
    assert (Hn := cfr_cells_static _ _ _ _ _ _ _ _ CFR H);
    cbn [cells_size csize Nat.add] in Hn;
    specialize (Hn ltac:(lia) ltac:(lia));
    specialize (Hn ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS;
                         split; [lia|]; split; [lia|]; cbn [rin_ivs fst snd app]; intros X;
                         repeat (destruct X as [X|X]; [lia|]); first [lia | apply CI_W_RANGE in X; unfold DC_CTX in X; lia])).

  Theorem finit_spec : init_crypto_full_stmt -> eclear_first_stmt -> finit_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros ICF ECL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd
           b0 ib u kold0 kold1 kold2 r36 r44 o80 o88 tsd sh oldcb r0 l0 h0 er0 eg0 dkold dr12 dr20
           Hf ROOM CST SLO1 SLO2 SLO3 SP16 BI STOP K1C C32 R36 C40 R44 LKC OD HC DK0 DK4 EG IC OC KC INB DKC DC8 DR12 DC16 DR20 C0 CBC TC TV USED NK KL KY0 KY1 KY2 KY3 SL0 SL2 SL3 RPL.
    unfold init_crypto_full_stmt in ICF. unfold eclear_first_stmt in ECL.
    pose proof (fxi_spec CI_EV CI_A CI_B CI_BIG CI_STK CI_W CI_PRE CI_FP CI_RES CTXI CI_W_RANGE CI_STK_POS CI_PRE_agree CI_FP_ok CI_RES_cfr) as FXI. unfold fxi_stmt in FXI.
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    subst tp.
    unfold FI_EV, ICF_STACK, ILS_STACK, CRS_STACK, ELF_STACK, ECL_STACK, EGSI_STACK, ITS_STACK, MTL_STACK, TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK,
           FXI_STACK, GDC_STACK, GLOBALS_TOP, LX_INIT, ERR_ONCE_CELL, RATP, IC_S, DC_S in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
    destruct ROOM as (RA & RB & RC). unfold NCRYPTO, LHA_MAX in *. change (Z.of_nat 4318) with 4318 in *. pose proof CI_NUMS as (NA0 & NB0 & NBIG0).
    change (3333664 + 8) with 3333672 in *. change (3333664 + 28) with 0x32de3c in *. change (3333664 + 32) with 0x32de40 in *. change (3333664 + 36) with 3333700 in *.
    change (3333664 + 40) with 3333704 in *. change (3333664 + 44) with 3333708 in *. change (3333664 + 80) with 3333744 in *. change (3333664 + 96) with 3333760 in *.
    change (3265744 + 4) with 3265748 in *.
    change (3333808 + 4) with 3333812 in *. change (3333808 + 8) with 3333816 in *. change (3333808 + 12) with 3333820 in *. change (3333808 + 16) with 3333824 in *. change (3333808 + 20) with 3333828 in *.
    destruct C0 as [cbs C0]. unfold DC_CTX, CTX_SIZE in C0.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj BI (conj STOP (conj K1C (conj C32 (conj R36 (conj C40 (conj R44 (conj LKC (conj OD (conj HC (conj DK0 (conj DK4 (conj EG (conj IC (conj OC (conj KC
               (conj INB (conj DKC (conj DC8 (conj DR12 (conj DC16 (conj DR20 (conj C0 (conj CBC (conj TC (conj USED (conj NK (conj KL (conj KY0 (conj KY1 (conj KY2 (conj KY3
               (conj SL0 (conj SL2 (conj SL3 RPL))))))))))))))))))))))))))))))))))) as CELLS.
    clear BI STOP K1C C32 R36 C40 R44 LKC OD HC DK0 DK4 EG IC OC KC INB DKC DC8 DR12 DC16 DR20 C0 CBC TC USED NK KL KY0 KY1 KY2 KY3 SL0 SL2 SL3 RPL.
    (* [comment removed for export] *)
    cprefix. step. step. th_frame 16%nat [8; 8]%nat ST. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (TR : forall A cs, rw_cells usegs m A cs -> A + Z.of_nat (cells_size cs) <= 3485696 -> rw_cells usegs mm A cs)
        by (intros A cs H HB; eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from]; lia]) end.
    destruct CELLS as (BI & STOP & K1C & C32 & R36 & C40 & R44 & LKC & OD & HC & DK0 & DK4 & EG & IC & OC & KC & INB & DKC & DC8 & DR12 & DC16 & DR20 & C0 & CBC & TC & USED
                       & NK & KL & KY0 & KY1 & KY2 & KY3 & SL0 & SL2 & SL3 & RPL).
    apply TR in RPL; [| cbn; lia]. apply TR in BI; [| cbn; lia]. apply TR in STOP; [| cbn; lia]. apply TR in K1C; [| cbn; lia]. apply TR in C32; [| cbn; lia]. apply TR in R36; [| cbn; lia].
    apply TR in C40; [| cbn; lia]. apply TR in R44; [| cbn; lia]. apply TR in LKC; [| cbn; lia]. apply TR in OD; [| cbn; lia]. apply TR in HC; [| cbn; lia].
    apply TR in DK0; [| cbn; lia]. apply TR in DK4; [| cbn; lia]. apply TR in EG; [| cbn; lia]. apply TR in IC; [| cbn; lia]. apply TR in OC; [| cbn; lia].
    apply TR in KC; [| cbn; lia]. apply TR in INB; [| cbn; lia]. apply TR in DKC; [| cbn; lia]. apply TR in DC8; [| cbn; lia]. apply TR in DR12; [| cbn; lia].
    apply TR in DC16; [| cbn; lia]. apply TR in DR20; [| cbn; lia]. apply TR in C0; [| cbn; lia]. apply TR in CBC; [| cbn; lia]. apply TR in TC; [| cbn; lia].
    apply TR in USED; [| cbn; lia]. apply TR in NK; [| cbn; lia]. apply TR in KL; [| cbn; lia]. apply TR in KY0; [| cbn; lia]. apply TR in KY1; [| cbn; lia].
    apply TR in KY2; [| cbn; lia]. apply TR in KY3; [| cbn; lia]. apply TR in SL0; [| cbn; lia]. apply TR in SL2; [| cbn; lia]. apply TR in SL3; [| cbn; lia].
    clear TR.
    chere.
    lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
    lazymatch goal with H : stk usegs m0 _ _ |- _ => rename H into ST0 end.
    lazymatch goal with H : mem_inv usegs m0 |- _ => rename H into MI0 end.
    assert (CSTa : cstate s LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -16)) (Z_to_bv 64 3344744) lo Bd).
    { eapply (cstate_seg _ _ _ _ _ m m0 _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MI0| | lia| lia| | rewrite unsigned_lit by lia; exact ST0| rewrite unsigned_lit by lia; lia].
      - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    assert (FRa : cframe (fun _ => False) FI_W (bv_unsigned sp) s LBall L m s LBall L m0).
    { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
    eapply climpl_seq.
    { eapply ICF with (lo := lo) (Bd := Bd); [clear - Hf; lia| unfold croom; lia| exact CSTa| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| reflexivity
        | exact BI| exact STOP| exact K1C| exact C32| exact R36| exact C40| exact R44| exact LKC| exact OD| exact HC| exact DK0| exact IC| exact OC| exact KC
        | exact CBC| exact TC| exact TV| exact USED| exact NK| exact KL| exact KY0| exact KY1| exact KY2| exact SL2]. }
    clear BI K1C C32 R36 C40 R44 LKC OD HC DK0 IC OC KC CBC TC TV USED NK KL KY0 KY1 KY2 SL2.
    intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & IRES).
    destruct IRES as (pk1 & pk2 & pm & psa & pn & pke & pl & pb & LK1 & LK2 & MK & SA & P & LKe & lh & B & u1 & pad & top & ne
                      & -> & ELS & FRESH1 & INM & INS & INP & INK2 & INK1 & RNGM & RNGS & RNGP & RNG1 & RNG2 & MC1 & MC2
                      & BI1 & K1C1 & C321 & C401 & LKC1 & OD1 & DK01 & IC1 & OC1 & KC1 & CBC1 & TC1 & USED1 & NK1 & KL1 & KY01 & KY11 & KY21 & SL21
                      & MKC & HDR & PBLK & HCE & NEF).
    destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
    cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia).
    unfold IC_S, RATP, ERR_ONCE_CELL in BI1, K1C1, C321, C401, LKC1, OD1, CBC1, TC1, USED1, HCE.
    change (3333664 + 28) with 0x32de3c in K1C1. change (3333664 + 32) with 0x32de40 in C321. change (3333664 + 40) with 3333704 in C401.
    change (3333664 + 80) with 3333744 in LKC1. change (3333664 + 96) with 3333760 in OD1.
    unfold ICF_W, IB_W, ILS_W, SHV_W, IC_S, RATP in FRM1. pose proof FRM1 as (CFR1 & KP1 & _). cbn [app] in CFR1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
    cst_static CFR1 STOP STOP1. cst_static CFR1 DK4 DK41. cst_static CFR1 EG EG1. cst_static CFR1 INB INB1. cst_static CFR1 DKC DKC1. cst_static CFR1 DC8 DC81.
    cst_static CFR1 DR12 DR121. cst_static CFR1 DC16 DC161. cst_static CFR1 DR20 DR201. cst_static CFR1 C0 C01. cst_static CFR1 KY3 KY31. cst_static CFR1 SL0 SL01.
    cst_static CFR1 SL3 SL31. cst_static CFR1 RPL RPL1.
    clear FR STOP DK4 EG INB DKC DC8 DR12 DC16 DR20 C0 KY3 SL0 SL3 RPL.
    assert (DK1 : rw_cells usegs m1 3265744 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 4294967295)]).
    { change [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 4294967295)] with ([C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 4294967295)]). apply rw_cells_app. split; [exact DK01|].
      cbn [cells_size csize Nat.add]. exact DK41. }
    clear DK01 DK41.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
    assert (FRM0 : cframe (fun _ => False) FI_W (bv_unsigned sp) s LBall L m st1 LBall1 L1 m1).
    { eapply cframe_call; [exact FRa| exact FRM1| lia| | intros q _ X; exact X].
      intros a X. unfold FI_W, ICF_W, IB_W, ILS_W, SHV_W, IC_S, RATP. cbn [rin_ivs fst snd app] in X |- *. lia. }
    clear FRa CSTa CFR1 FRM1.
    (* [comment removed for export] *)
    cprefix. step. chere.
    eapply climpl_seq.
    { eapply ECL with (lo := lo) (Bd := Bd); [clear - Hf FU1; lia| clear - RA RB RC GR1 NA0 NB0 NBIG0; unfold croom, cgrow in *; lia| exact CST1| rewrite unsigned_lit by lia; lia
        | exact STOP1| exact C321| exact OD1| exact OC1| exact KC1| exact TC1| exact SL21| exact INM| exact INS| exact INP| exact MKC| exact HDR| exact NEF| exact PBLK
        | exact DK1| exact SL01| exact USED1| exact EG1| exact CBC1]. }
    clear HDR PBLK SL01 USED1 EG1 CBC1.
    intros f2 L2 st2 ms2 (v2 & m2 & LBall2 & RET2 & FU2 & GR2 & CST2 & FRM2 & ERES).
    destruct ERES as (pe & ptn & ph & pg & psk & plk & pd & E & N & H & G & SK & LK & D & u2 & top2 & ne2
                      & ELB & EL & RNGE & RNGN & RNGH & RNGG & RNGSK & RNGLK & RNGD & ESC & HDR & PBLK & SL02 & USED2 & EG2 & CBC2 & HN & NC & GC & SKC & LKM & DC & NE0).
    destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
    cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia).
    subst LBall2 L2. unfold RATP in USED2, CBC2.
    unfold EGSI_W, RATP in FRM2. pose proof FRM2 as (CFR2 & KP2 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR1 ltac:(lia)) as FR2.
    unfold err_statics in HCE. unfold mutex_cells in MC1, MC2.
    cst_static CFR2 STOP1 STOP2. cst_static CFR2 INB1 INB2. cst_static CFR2 DKC1 DKC2. cst_static CFR2 DC81 DC82. cst_static CFR2 DR121 DR122. cst_static CFR2 DC161 DC162.
    cst_static CFR2 DR201 DR202. cst_static CFR2 C01 C02. cst_static CFR2 KY31 KY32. cst_static CFR2 SL31 SL32. cst_static CFR2 BI1 BI2. cst_static CFR2 K1C1 K1C2.
    cst_static CFR2 C321 C322. cst_static CFR2 C401 C402. cst_static CFR2 LKC1 LKC2. cst_static CFR2 OD1 OD2. cst_static CFR2 IC1 IC2. cst_static CFR2 OC1 OC2.
    cst_static CFR2 KC1 KC2. cst_static CFR2 TC1 TC2. cst_static CFR2 NK1 NK2. cst_static CFR2 KL1 KL2. cst_static CFR2 KY01 KY02. cst_static CFR2 KY11 KY12.
    cst_static CFR2 KY21 KY22. cst_static CFR2 SL21 SL22. cst_static CFR2 HCE HCE2. cst_static CFR2 DK1 DK2. cst_static CFR2 RPL1 RPL2.
    assert (NTM : ~ (pm = psa \/ pm = pn)).
    { intros [X|X]; [exact (blk_ids_ne _ _ _ _ _ _ _ ND1 INM INS ltac:(lia) X)| exact (blk_ids_ne _ _ _ _ _ _ _ ND1 INM INP ltac:(lia) X)]. }
    assert (NT1 : ~ (pk1 = psa \/ pk1 = pn)).
    { intros [X|X]; [exact (blk_ids_ne _ _ _ _ _ _ _ ND1 INK1 INS ltac:(lia) X)| exact (blk_ids_ne _ _ _ _ _ _ _ ND1 INK1 INP ltac:(lia) X)]. }
    assert (NT2 : ~ (pk2 = psa \/ pk2 = pn)).
    { intros [X|X]; [exact (blk_ids_ne _ _ _ _ _ _ _ ND1 INK2 INS ltac:(lia) X)| exact (blk_ids_ne _ _ _ _ _ _ _ ND1 INK2 INP ltac:(lia) X)]. }
    pose proof RNGM as (M0 & _ & _ & M72 & MIMG). pose proof RNG1 as (LK1P & _ & _ & LK1C & LK1IMG). pose proof RNG2 as (LK2P & _ & _ & LK2C & LK2IMG).
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pm, MK, 72) CFR2 MKC INM NTM ltac:(unfold blk_addr; cbn [fst snd]; lia)
                  ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as MKC2.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk1, LK1, 40) CFR2 MC1 INK1 NT1 ltac:(unfold blk_addr; cbn [fst snd]; lia)
                  ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as MC12.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk2, LK2, 40) CFR2 MC2 INK2 NT2 ltac:(unfold blk_addr; cbn [fst snd]; lia)
                  ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; lia)) as MC22.
    clear FR1 STOP1 INB1 DKC1 DC81 DR121 DC161 DR201 C01 KY31 SL31 BI1 K1C1 C321 C401 LKC1 OD1 IC1 OC1 KC1 TC1 NK1 KL1 KY01 KY11 KY21 SL21 HCE DK1 MKC MC1 MC2 RPL1.
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia.
    destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 NDL2]. cbn [map blk_id fst] in ND2, NDL2.
    assert (LIFT1 : forall q, In q (map blk_id LBall) \/ In q (map fst L) -> In q (map blk_id LBall1) \/ In q (map fst L1)).
    { intros q [Hq|Hq]; [left|right]; apply in_map_iff in Hq; destruct Hq as (bq & <- & Hb); apply in_map_iff.
      - exists bq. split; [reflexivity| exact (proj1 KP1 bq Hb (fun X => X))].
      - destruct bq as [q nm]. exists (q, nm). split; [reflexivity| exact (proj2 KP1 q nm Hb (fun X => X))]. }
    assert (FRM02 : cframe (fun _ => False) FI_W (bv_unsigned sp) s LBall L m st2
                      ((ptn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: (pe, E, 904) :: LBall1)
                      ((ptn, 32) :: (pd, 32) :: (plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: (pe, 904) :: L1) m2).
    { eapply cframe_call; [exact FRM0| exact FRM2| lia| |].
      - intros a X. unfold FI_W, ICF_W, IB_W, ILS_W, SHV_W, EGSI_W, IC_S, RATP. cbn [rin_ivs fst snd app] in X |- *. lia.
      - intros q Hq _ X. apply (FRESH1 q Hq). cbn [In]. clear - X. destruct X as [X|X]; subst; auto 10. }
    clear FRM0 CFR2 FRM2.
    (* [comment removed for export] *)
    cprefix. step. step. step. chere.
    assert (CIP : CI_PRE ((ptn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: (pe, E, 904) :: LBall1)
                         ((ptn, 32) :: (pd, 32) :: (plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: (pe, 904) :: L1) m2).
    { apply CI_PRE_intro. unfold ci_site, IC_S, ERR_ONCE_CELL, err_statics.
      change (3333664 + 8) with 3333672. change (3333664 + 28) with 0x32de3c. change (3333664 + 32) with 0x32de40. change (3333664 + 40) with 3333704.
      change (3333664 + 80) with 3333744. change (3333664 + 96) with 3333760.
      exists LK1, LK2, G, LKe, lh. repeat match goal with |- _ /\ _ => split end.
      - exact BI2. - exact STOP2. - exact K1C2. - exact C322. - exact C402. - exact LKC2. - exact OD2. - exact EG2. - exact IC2. - exact OC2. - exact KC2. - exact HCE2.
      - exact RPL2. }
    eapply climpl_seq.
    { eapply FXI with (lo := lo) (B := Bd); [clear - Hf FU1 FU2; lia| clear - RA RB RC GR1 GR2 NA0 NB0 NBIG0; unfold croom, cgrow in *; lia| exact CST2| rewrite unsigned_lit by lia; lia| rewrite ?unsigned_lit by lia; lia
        | reflexivity| reflexivity
        | exact INB2| exact DKC2| exact DC82| exact DR122| exact DC162| exact DR202| eexists; exact C02| exact CBC2| exact TC2| exact NK2| exact KL2| exact KY32| exact KY22
        | rewrite unsigned_lit by lia; lia| exact SL32| exact CIP]. }
    clear INB2 DKC2 DC82 DR122 DC162 DR202 C02 CBC2 TC2 NK2 KL2 KY32 SL32 CIP.
    intros f3 L3 st3 ms3 (v3 & m3 & LBall3 & RET3 & FU3 & GR3 & CST3 & FRM3 & XRES).
    destruct XRES as ((pkx & LKX & INKX & RKX & MCX & GLK & FRESHX & CRES) & INB3 & KC3 & C83 & R123 & C163 & R203 & CBC3 & TC3 & NK3 & KL3 & KY33 & SL33).
    destruct RET3 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
    cret_lit. repeat (rewrite unsigned_lit in FRM3 by lia).
    unfold DC_S, RATP, DC_GLOBAL_LOCK in INB3, KC3, C83, R123, C163, R203, CBC3, TC3, GLK.
    change (3333808 + 4) with 3333812 in KC3. change (3333808 + 8) with 3333816 in C83. change (3333808 + 12) with 3333820 in R123. change (3333808 + 16) with 3333824 in C163.
    change (3333808 + 20) with 3333828 in R203.
    unfold GDC_W, DC_S, RATP in FRM3. pose proof FRM3 as (CFR3 & KP3 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR2 ltac:(lia)) as FR3.
    cst_staticW CFR3 BI2 BI3. cst_staticW CFR3 STOP2 STOP3. cst_staticW CFR3 K1C2 K1C3. cst_staticW CFR3 C322 C323. cst_staticW CFR3 C402 C403. cst_staticW CFR3 LKC2 LKC3.
    cst_staticW CFR3 OD2 OD3. cst_staticW CFR3 EG2 EG3. cst_staticW CFR3 IC2 IC3. cst_staticW CFR3 OC2 OC3. cst_staticW CFR3 KC2 KC23. cst_staticW CFR3 HCE2 HCE3.
    cst_staticW CFR3 DK2 DK3. cst_staticW CFR3 USED2 USED3. cst_staticW CFR3 KY02 KY03. cst_staticW CFR3 KY12 KY13. cst_staticW CFR3 KY22 KY23. cst_staticW CFR3 SL02 SL03.
    cst_staticW CFR3 SL22 SL23. cst_staticW CFR3 RPL2 RPL3.
    unfold sa_hdr in HDR. unfold sk_cells in SKC. unfold mutex_cells in LKM, MCX. unfold es_clean in ESC.
    pose proof RNGE as (E0 & _ & _ & E904 & EIMG). pose proof RNGS as (S0 & _ & _ & S32 & SIMG). pose proof RNGP as (P0 & _ & _ & P128 & PIMG).
    pose proof RNGH as (H0 & _ & _ & H8 & HIMG). pose proof RNGN as (N0 & _ & _ & N32 & NIMG). pose proof RNGG as (G0 & _ & _ & G16 & GIMG).
    pose proof RNGSK as (SK0 & _ & _ & SK56 & SKIMG). pose proof RNGLK as (LK0 & _ & _ & LK40 & LKIMG). pose proof RNGD as (D0 & _ & _ & D32 & DIMG).
    set (LB2 := (ptn, N, 32) :: (pd, D, 32) :: (plk, LK, 40) :: (psk, SK, 56) :: (pg, G, 16) :: (ph, H, 8) :: (pe, E, 904) :: LBall1) in *.
    assert (JTN : In (ptn, N, 32) LB2) by (subst LB2; left; reflexivity).
    assert (JD : In (pd, D, 32) LB2) by (subst LB2; right; left; reflexivity).
    assert (JLK : In (plk, LK, 40) LB2) by (subst LB2; do 2 right; left; reflexivity).
    assert (JSK : In (psk, SK, 56) LB2) by (subst LB2; do 3 right; left; reflexivity).
    assert (JG : In (pg, G, 16) LB2) by (subst LB2; do 4 right; left; reflexivity).
    assert (JH : In (ph, H, 8) LB2) by (subst LB2; do 5 right; left; reflexivity).
    assert (JE : In (pe, E, 904) LB2) by (subst LB2; do 6 right; left; reflexivity).
    assert (JM : In (pm, MK, 72) LB2) by (subst LB2; do 7 right; exact INM).
    assert (JS : In (psa, SA, 32) LB2) by (subst LB2; do 7 right; exact INS).
    assert (JP : In (pn, P, 128) LB2) by (subst LB2; do 7 right; exact INP).
    assert (JK1 : In (pk1, LK1, 40) LB2) by (subst LB2; do 7 right; exact INK1).
    assert (JK2 : In (pk2, LK2, 40) LB2) by (subst LB2; do 7 right; exact INK2).
    Ltac cblk3 CFR H b HIN Hn :=
      pose proof (cfr_cells_block _ _ _ _ _ _ _ _ b CFR H HIN (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia)
                    ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add repeat app length]; lia)) as Hn.
    cblk3 CFR3 ESC (pe, E, 904) JE ESC3. cblk3 CFR3 MKC2 (pm, MK, 72) JM MKC3. cblk3 CFR3 HDR (psa, SA, 32) JS HDR3. cblk3 CFR3 PBLK (pn, P, 128) JP PBLK3.
    cblk3 CFR3 HN (ph, H, 8) JH HN3. cblk3 CFR3 NC (ptn, N, 32) JTN NC3. cblk3 CFR3 GC (pg, G, 16) JG GC3. cblk3 CFR3 SKC (psk, SK, 56) JSK SKC3.
    cblk3 CFR3 LKM (plk, LK, 40) JLK LKM3. cblk3 CFR3 DC (pd, D, 32) JD DC3. cblk3 CFR3 MC12 (pk1, LK1, 40) JK1 MC13. cblk3 CFR3 MC22 (pk2, LK2, 40) JK2 MC23.
    clear ESC MKC2 HDR PBLK HN NC GC SKC LKM DC MC12 MC22 BI2 STOP2 K1C2 C322 C402 LKC2 OD2 EG2 IC2 OC2 KC2 HCE2 DK2 USED2 KY02 KY12 KY22 SL02 SL22 FR2 RPL2.
    assert (IN3 : forall b, In b LB2 -> In b LBall3) by (intros b Hb; exact (proj1 KP3 b Hb (fun X => X))).
    pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
    pose proof DK3 as DKX. change [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 4294967295)] with ([C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 4294967295)]) in DKX.
    apply (proj1 (rw_cells_app usegs _ _ _ _)) in DKX. destruct DKX as [DK03 DK43]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in DK43.
    (* [comment removed for export] *)
    cprefix. step. step. step.
    lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into STe end.
    release_frame FR3 STe (bv_unsigned sp).
    step.
    lazymatch goal with H : stk usegs m3 lo (bv_unsigned sp) |- _ => rename H into STf end.
    chere. apply climpl_done.
    exists (Z_to_bv 64 1), m3, LBall3.
    split; [unfold cret; do 14 eexists; reflexivity|].
    split; [clear - Hf FU1 FU2 FU3; lia|].
    split; [clear - GR1 GR2 GR3 NA0 NB0 NBIG0; unfold cgrow in *; lia|].
    split. { eapply (cstate_seg _ _ _ _ _ m3 m3 _ sp _ lo Bd (bv_unsigned sp)); [exact CST3| apply munch_refl| apply wmono_refl| exact MI3| apply Forall_nil| lia| exact SPB| exact I| exact STf| exact SPB]. }
    split. { eapply cframe_call; [exact FRM02| exact FRM3| lia| | intros q _ _ X; exact X].
      intros a X. unfold FI_W, ICF_W, IB_W, ILS_W, SHV_W, EGSI_W, GDC_W, IC_S, DC_S, RATP. cbn [rin_ivs fst snd app] in X |- *.
      repeat (destruct X as [X|X]; [lia|]). do 26 right. exact X. }
    split; [reflexivity|].
    exists pe, pm, psa, pn, ph, ptn, pg, psk, plk, pd, pk1, pk2, pkx, E, MK, SA, P, H, N, G, SK, LK, D, LK1, LK2, LKX, LKe, lh, u2, pad, top2, ne2.
    assert (LIFT2 : forall q, In q (map blk_id LBall) \/ In q (map fst L) ->
              In q (map blk_id LB2) \/ In q (map fst ((ptn, 32) :: (pd, 32) :: (plk, 40) :: (psk, 56) :: (pg, 16) :: (ph, 8) :: (pe, 904) :: L1))).
    { intros q Hq. destruct (LIFT1 q Hq) as [X|X]; [left|right]; [subst LB2|]; cbn [map blk_id fst]; do 7 right; exact X. }
    repeat match goal with |- _ /\ _ => split end.
    all: try (apply IN3; assumption).
    - exact INKX.
    - intros q Hq HIn. pose proof (LIFT1 q Hq) as Hq1.
      assert (N7 : ~ In q [ptn; pd; plk; psk; pg; ph; pe]).
      { destruct Hq1 as [H1|H1].
        - apply (nodup_app_disj [ptn; pd; plk; psk; pg; ph; pe] (map blk_id LBall1) q); [exact ND2| exact H1].
        - apply (nodup_app_disj [ptn; pd; plk; psk; pg; ph; pe] (map fst L1) q); [exact NDL2| exact H1]. }
      pose proof (FRESH1 q Hq) as N5. pose proof (FRESHX q (LIFT2 q Hq)) as NX.
      clear - HIn N7 N5 NX. cbn [In] in HIn, N7, N5.
      decompose [or] HIn; clear HIn; subst;
        first [exfalso; apply N7; solve [auto 20] | exfalso; apply N5; solve [auto 20] | exfalso; apply NX; reflexivity | contradiction].
    - exact ESC3. - exact MKC3. - unfold sa_hdr; exact HDR3. - exact PBLK3. - exact HN3. - exact NC3. - exact GC3. - unfold sk_cells; exact SKC3.
    - unfold mutex_cells; exact LKM3. - exact DC3. - unfold mutex_cells; exact MC13. - unfold mutex_cells; exact MC23. - unfold mutex_cells; exact MCX.
    - exact BI3. - exact STOP3. - exact K1C3. - exact C323. - exact C403. - exact LKC3. - exact OD3. - exact EG3. - exact IC3. - exact OC3. - exact KC23.
    - exact INB3. - exact KC3. - exact C83. - exact R123. - exact C163. - exact R203. - exact GLK. - unfold ERR_ONCE_CELL, err_statics; exact HCE3.
    - exact DK03.
    - exact DK43.
    - exact CBC3. - exact TC3. - exact USED3. - exact NK3. - exact KL3. - exact KY03. - exact KY13. - exact KY23. - exact KY33. - exact SL03. - exact SL23. - exact SL33.
    - exact RPL3.
    - exact NE0.
    - exact CRES.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma fi_w_client : forall a, rin_ivs FI_W a -> rin_ivs LXW_CLIENT a.
  Proof.
    intros a X. unfold FI_W, ICF_W, IB_W, ILS_W, SHV_W, EGSI_W, GDC_W, IC_S, DC_S, RATP in X.
    unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY. cbn [rin_ivs fst snd app] in X |- *.
    repeat (destruct X as [X|X]; [lia|]). apply CI_W_RANGE in X. unfold DC_CTX in X. lia.
  Qed.

  Variable C : cli_sig.

  (* [comment removed for export] *)
  Definition finit_pre (m : mem) : Prop :=
    exists (b0 ib u : byte) (kold0 kold1 kold2 r36 r44 o80 o88 tsd sh oldcb r0 l0 h0 er0 eg0 dkold dr12 dr20 : word),
       rw_cells usegs m IC_S [C1 b0] /\ rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] /\ rw_cells usegs m (IC_S + 28) [C4 kold1]
    /\ rw_cells usegs m (IC_S + 32) [C4 z64] /\ rw_cells usegs m (IC_S + 36) [C4 r36] /\ rw_cells usegs m (IC_S + 40) [C4 z64] /\ rw_cells usegs m (IC_S + 44) [C4 r44]
    /\ rw_cells usegs m (IC_S + 80) [C8 o80; C8 o88] /\ rw_cells usegs m (IC_S + 96) [C8 z64]
    /\ rw_cells usegs m ERR_ONCE_CELL [C4 z64; C4 r0; C8 l0; C8 h0]
    /\ rw_cells usegs m 0x31d4d0 [C4 kold0] /\ rw_cells usegs m (0x31d4d0 + 4) [C4 (Z_to_bv 64 0xffffffff)]
    /\ rw_cells usegs m 0x32de90 [C4 z64; C4 er0; C8 eg0]
    /\ rw_cells usegs m 0x32dea0 [C1 ib] /\ rw_cells usegs m 0x32dea4 [C4 z64] /\ rw_cells usegs m 0x32dea8 [C4 kold2]
    /\ rw_cells usegs m DC_S [C1 (Z_to_bv 8 0)] /\ rw_cells usegs m (DC_S + 4) [C4 dkold] /\ rw_cells usegs m (DC_S + 8) [C4 z64] /\ rw_cells usegs m (DC_S + 12) [C4 dr12]
    /\ rw_cells usegs m (DC_S + 16) [C4 z64] /\ rw_cells usegs m (DC_S + 20) [C4 dr20] /\ ctx0 m
    /\ rw_cells usegs m (RATP + -96) [C8 oldcb] /\ rw_cells usegs m (RATP + -88) [C8 tsd] /\ (tsd = z64 \/ tsd = Z_to_bv 64 0x351cd0) /\ rw_cells usegs m (RATP + -150) [C1 u]
    /\ rw_cells usegs m 0x351c90 [C4 z64] /\ rw_cells usegs m 0x351c98 [C4 z64; C4 z64; C4 sh]
    /\ rw_cells usegs m 0x351890 [C8 z64] /\ rw_cells usegs m (0x351890 + 8 * 1) [C8 z64] /\ rw_cells usegs m (0x351890 + 8 * 2) [C8 z64] /\ rw_cells usegs m (0x351890 + 8 * 3) [C8 z64]
    /\ rw_cells usegs m 0x351cd0 [C8 z64] /\ rw_cells usegs m (0x351cd0 + 8 * 2) [C8 z64] /\ rw_cells usegs m (0x351cd0 + 8 * 3) [C8 z64]
    /\ rw_cells usegs m 0x351010 [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells usegs m 0x32df38 [C8 z64].
  Hypothesis CLI0_pre : forall m, CLI0 C m -> finit_pre m.
  (* [comment removed for export] *)
  Hypothesis CLI_post : forall (oldcb sh : word) (LB LBall' : list block) (L' : @clist bptr) (CLB : list block) (m' : mem) (s' : PState) (sp tp : word) (lo B : Z),
    cstate s' LBall' LB L' m' sp tp lo B -> Permutation LBall' (CLB ++ LB) -> cl_rel CLB L' ->
    finit_res oldcb sh LB [] (Z_to_bv 64 1) LBall' L' m' -> rw_cells usegs m' 0x32df38 [C8 z64] -> CLI C m' CLB.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CI_BUDGET : (CI_EV <= 3415)%nat /\ CI_A <= 3700 /\ CI_B <= 30 /\ CI_BIG <= 800000 /\ CI_STK <= 65264.

  Theorem rfuzz_init_proof : init_crypto_full_stmt -> eclear_first_stmt -> rfuzz_init_stmt C.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros ICF ECL. unfold rfuzz_init_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB flags lo B errv canary
           HP LXS FL SEW SSP AV SPB HB ST LO GLO SLO ERR TP MI AL FC CL0.
    pose proof (cstate_init s LB m sp tp lo B flags errv HP LXS FL AV SPB ST LO GLO ERR TP MI) as CST.
    destruct (CLI0_pre m CL0) as (b0 & ib & u & kold0 & kold1 & kold2 & r36 & r44 & o80 & o88 & tsd & sh & oldcb & r0 & l0 & h0 & er0 & eg0 & dkold & dr12 & dr20 & PRE).
    destruct PRE as (BI & STOP & K1C & C32 & R36 & C40 & R44 & LKC & OD & HC & DK0 & DK4 & EG & IC & OC & KC & INB & DKC & DC8 & DR12 & DC16 & DR20 & C0 & CBC & TC & TV & USED
                     & NK & KL & KY0 & KY1 & KY2 & KY3 & SL0 & SL2 & SL3 & RPL & IP12).
    pose proof CI_BUDGET as (BEV & BA & BB & BBIG & BSTK).
    unfold fuzz_init. eapply climpl_close.
    { eapply (finit_spec ICF ECL) with (lo := lo) (Bd := B);
        [unfold FI_EV, INIT_FUEL, NCRYPTO; clear - BEV; lia
        | unfold croom, CAP_A, CAP_B, BIG_ROOM, NCRYPTO, LHA_MAX; change (Z.of_nat 4318) with 4318; unfold cntA, cntB; cbn [bigsum length List.filter fold_right Z.of_nat]; clear - BA BB BBIG; lia
        | exact CST
        | unfold ICF_STACK, ILS_STACK, CRS_STACK, ELF_STACK, LX_INIT_STACK in *; lia
        | unfold ECL_STACK, EGSI_STACK, ITS_STACK, MTL_STACK, TEVENT_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, LX_INIT_STACK in *; lia
        | unfold FXI_STACK, GDC_STACK, LX_INIT_STACK in *; lia
        | exact AL
        | exact BI| exact STOP| exact K1C| exact C32| exact R36| exact C40| exact R44| exact LKC| exact OD| exact HC| exact DK0| exact DK4| exact EG| exact IC| exact OC| exact KC
        | exact INB| exact DKC| exact DC8| exact DR12| exact DC16| exact DR20| exact C0| exact CBC| exact TC| exact TV| exact USED| exact NK| exact KL
        | exact KY0| exact KY1| exact KY2| exact KY3| exact SL0| exact SL2| exact SL3| exact RPL]. }
    cbv beta. intros f' L' s' ms' (v & m' & LBall' & RET & FU & GR & CST' & FRM & -> & RES).
    destruct (init_exit (fun _ => False) FI_W s LB m s' LBall' L' m' sp tp lo B canary CST' FRM fi_w_client ltac:(intros b _ X; exact X) HP SEW SSP HB
                ltac:(unfold CL_ROOM_A, CL_ROOM_B, CL_ROOM_BIG, CAP_A, CAP_B, BIG_ROOM, NCRYPTO, LHA_MAX in *; unfold cgrow, cntA, cntB in GR |- *;
                      cbn [bigsum length List.filter fold_right Z.of_nat] in GR |- *; change (Z.of_nat 4318) with 4318 in GR; clear - GR BA BB BBIG; lia))
      as (CLB & errv' & PERM & REL & ENV & PRES & SO & FA).
    exists CLB. split; [exact REL|].
    destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
    unfold rfuzz_ret. exists u0, u1, u2, (Z_to_bv 64 1), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m'.
    split; [reflexivity|].
    split. { split; [exists errv'; exact ENV|]. split; [exact FC|]. split; [exact PRES|]. split; [exact SO| exact FA]. }
    split; [reflexivity|]. split; [| exact I].
    eapply (CLI_post oldcb sh LB LBall' L' CLB m' s' sp tp lo B CST' PERM REL); [split; [reflexivity| exact RES]|].
    eapply cfr_cells_static; [exact (proj1 FRM)| exact IP12| clear; lia| cbn; clear; lia|].
    intros a Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    split; [unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; clear - Ha; lia|].
    split; [unfold LX_FLAGS; clear - Ha; lia|].
    intros X. unfold FI_W, ICF_W, IB_W, ILS_W, SHV_W, EGSI_W, GDC_W, IC_S, DC_S, RATP in X. cbn [rin_ivs fst snd app] in X.
    repeat (destruct X as [X|X]; [clear - X Ha; lia|]). exact (CI_W_IP12 a X Ha).
  Qed.
End Top.
End WithCeiling0.
