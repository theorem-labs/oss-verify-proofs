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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex Th_key Th_once. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_T_once Fz_T_local Fz_T_lock Fz_T_lock_new Fz_I3_base.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

Definition DC_S : Z := 0x32deb0.                 (* [comment removed for export] *)
Definition DC_CTX : Z := 0x32dec8.               (* [comment removed for export] *)
Definition DC_GLOBAL_LOCK : Z := 0x32ded0.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dctki_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (lo : Z) (kold r12 sh w : word),
  tp = Z_to_bv 64 RATP ->
  rw_cells usegs m (DC_S + 4) [C4 kold] -> rw_cells usegs m (DC_S + 12) [C4 r12] ->
  rw_cells usegs m (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)] ->
  rw_cells usegs m 0x351c90 [C4 (Z_to_bv 64 2)] -> rw_cells usegs m 0x351c98 [C4 z64; C4 z64; C4 sh] ->
  rw_cells usegs m (0x351890 + 8 * 3) [C8 z64] -> ro_cells usegs m (0x351890 + 8 * 2) [C8 w] -> bv_unsigned w <> 0 ->
  stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 144 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
         ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (DC_S + 4, DC_S + 8); (DC_S + 12, DC_S + 16); (0x351c90, 0x351c9c);
                (0x351890 + 8 * 3, 0x351890 + 8 * 3 + 8); (RATP + -88, RATP + -80)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (DC_S + 4) [C4 (Z_to_bv 64 3)] /\ rw_cells usegs m' (DC_S + 12) [C4 (Z_to_bv 64 1)]
      /\ rw_cells usegs m' (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)]
      /\ rw_cells usegs m' 0x351c90 [C4 (Z_to_bv 64 3)] /\ rw_cells usegs m' 0x351c98 [C4 z64; C4 z64; C4 sh]
      /\ rw_cells usegs m' (0x351890 + 8 * 3) [C8 (Z_to_bv 64 0x2bdf1c)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe47d0) fc None m (seg_rom usegs)).

Theorem dctki_proof : dctki_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until w. intros -> KC R12 TSD NK KL KY3 KY2 WNZ ST GLO SLO MI.
  unfold DC_S, RATP, GLOBALS_TOP in *. unfold ceil_window in CEIL_RANGE__.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  change (3333808 + 4) with 3333812 in *. change (3333808 + 12) with 3333820 in *. change (3333808 + 8) with 3333816. change (3333808 + 16) with 3333824.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (3333812, 3333816); (3333820, 3333824); (0x351c90, 0x351c9c);
                           (0x351890 + 8 * 3, 0x351890 + 8 * 3 + 8); (3344744 + -88, 3344744 + -80)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  step. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 3 step. step. do 2 step. do 2 step. step.
  tcall (T_init_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 2 3 sh kold w (Z_to_bv 64 0x351cd0)).
  all: try first [eassumption | reflexivity | lia | right; reflexivity | right; split; [reflexivity| lia]].
  cbv beta delta [mkR]. try th_ret_lit.
  change (if bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) then Z_to_bv 64 2875164 else Z_to_bv 64 0) with (Z_to_bv 64 2875164) in *.
  step. cstep. do 3 step.
  lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into STe end.
  lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -32) _ |- _ => release_frame H STe (bv_unsigned sp) end.
  step. step.
  apply evt_done. do 9 eexists. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CTX_SIZE : nat := 328.
Definition ctx0 (m : mem) : Prop := exists bs, rw_cells usegs m DC_CTX [CB CTX_SIZE bs].

Section CtxInit.
  Variables (CI_EV : nat) (CI_A CI_B CI_BIG CI_STK : Z) (CI_W : list (Z * Z)).
  (* [comment removed for export] *)
  Variable CI_PRE : list block -> @clist bptr -> mem -> Prop.
  Variable CI_FP : Z -> Prop.
  Definition FXI_PW : list (Z * Z) := [(DC_S, DC_S + 24); (0x351c90, 0x351c9c); (0x351890 + 8 * 3, 0x351890 + 8 * 3 + 8); (RATP + -96, RATP + -80)].
  (* [comment removed for export] *)
  Variable CI_RES : bptr -> list block -> @clist bptr -> mem -> Prop.
  Definition FXI_AW : list (Z * Z) := [(DC_S, DC_S + 24); (RATP + -96, RATP + -80)].

  (* [comment removed for export] *)
  Definition ctxi_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
    fun v LBall' L' m' => v = Z_to_bv 64 1 /\ exists (pk : bptr) (LK : Z),
         In (pk, LK, 40) LBall' /\ rblock_range LK 40 /\ rw_cells usegs m' LK (mutex_cells z64 z64)
      /\ rw_cells usegs m' DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)]
      /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> q <> pk)
      /\ CI_RES pk LBall' L' m'.

  Definition context_init_abs_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
    (CI_EV <= f)%nat -> croom L CI_A CI_B CI_BIG -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CI_STK -> bv_unsigned sp mod 16 = 0 ->
    a0 = Z_to_bv 64 DC_CTX -> ctx0 m -> CI_PRE LBall L m ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe4374) fc None m (seg_rom usegs))
           (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) CI_W CI_EV CI_A CI_B CI_BIG (ctxi_res LBall L)).

  Hypothesis CTXI : context_init_abs_stmt.
  Hypothesis CI_W_RANGE : forall a, rin_ivs CI_W a -> DC_CTX <= a < DC_CTX + 328.
  Hypothesis CI_STK_POS : 112 <= CI_STK.
  Hypothesis CI_NUMS : 0 <= CI_A /\ 0 <= CI_B /\ 0 <= CI_BIG.
  Hypothesis CI_PRE_agree : forall LBall L m m', agree_on CI_FP m m' -> CI_PRE LBall L m -> CI_PRE LBall L m'.
  Hypothesis CI_FP_ok : forall a, CI_FP a -> 0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS /\ ~ rin_ivs FXI_PW a.
  Hypothesis CI_RES_cfr : forall pk LBall' L' m m' SPX, CI_RES pk LBall' L' m -> cfr (fun q => q = pk) FXI_AW SPX LBall' m m' -> CI_RES pk LBall' L' m'.

  (* [comment removed for export] *)
  Lemma ci_pre_seg : forall W LBall L m m', CI_PRE LBall L m -> munch W m m' -> wmono usegs m m' ->
    (forall a, 0x2c0000 <= a < 0x353000 -> ~ ralloc_static a -> a <> LX_FLAGS -> ~ rin_ivs FXI_PW a -> outside W a) -> CI_PRE LBall L m'.
  Proof.
    intros W LBall L m m' H MU WM HW. eapply CI_PRE_agree; [| exact H]. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|].
    intros a Ha. cbv beta. destruct (CI_FP_ok a Ha) as (A1 & A2 & A3 & A4). exact (HW a A1 A2 A3 A4).
  Qed.
  Ltac ci_pre_here CIP MU WM :=
    lazymatch type of MU with munch _ ?m0 ?m1 =>
      lazymatch type of CIP with CI_PRE ?LBx ?Lx m0 =>
        assert (CI_PRE LBx Lx m1) by
          (eapply (ci_pre_seg _ _ _ m0 m1); [exact CIP| exact MU| exact WM|];
           intros a__ A1__ A2__ A3__ A4__; unfold FXI_PW, DC_S, RATP in A4__; cbn [rin_ivs fst snd] in A4__;
           unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in A2__;
           cbn [outside]; lia) end end.

  (* [comment removed for export] *)
  Definition DCDI_W : list (Z * Z) := (DC_S, DC_S + 1) :: (DC_S + 20, DC_S + 24) :: CI_W.
  Definition dcdi_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
    fun _ LBall' L' m' => (exists (pk : bptr) (LK : Z),
         In (pk, LK, 40) LBall' /\ rblock_range LK 40 /\ rw_cells usegs m' LK (mutex_cells z64 z64)
      /\ rw_cells usegs m' DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> q <> pk)
      /\ CI_RES pk LBall' L' m')
      /\ rw_cells usegs m' DC_S [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' (DC_S + 20) [C4 (Z_to_bv 64 1)].

  Definition dcdi_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z) (b0 : byte) (r20 : word),
    (CI_EV <= f)%nat -> croom L CI_A CI_B CI_BIG -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - (32 + CI_STK) -> bv_unsigned sp mod 16 = 0 ->
    rw_cells usegs m DC_S [C1 b0] -> rw_cells usegs m (DC_S + 20) [C4 r20] -> ctx0 m -> CI_PRE LBall L m ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe4814) fc None m (seg_rom usegs))
           (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) DCDI_W CI_EV CI_A CI_B CI_BIG (dcdi_res LBall L)).

  Theorem dcdi_spec : dcdi_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd b0 r20
           Hf ROOM CST SLO SP16 INB R20 C0 CIP.
    pose proof CTXI as CI. unfold context_init_abs_stmt in CI.
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold DC_S, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
    change (3333808 + 20) with 3333828 in R20. destruct C0 as [cbs C0]. unfold DC_CTX, CTX_SIZE in C0.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    cprefix. step. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 3 step. step. do 2 step. step. step. chere.
    lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into ma end.
    lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
    lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
    assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo Bd).
    { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
      - constructor; [apply cwin_stack; lia| constructor].
      - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    assert (FRa : cframe (fun _ : bptr => False) DCDI_W (bv_unsigned sp) s LBall L m s LBall L ma).
    { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
    ci_pre_here CIP MU WM.
    eapply climpl_seq.
    { eapply CI with (lo := lo) (B := Bd); [lia| exact ROOM| exact CSTa| rewrite unsigned_lit by lia; lia| rewrite ?unsigned_lit by lia; lia| reflexivity| eexists; eassumption| assumption]. }
    intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (-> & pk & LK & INK & RK & MC & GLK & FRESH & CRES)).
    destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
    cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia).
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
    assert (INB1 := cfr_cells_static _ _ _ _ _ _ _ _ CFR1 INB). cbn [cells_size csize Nat.add] in INB1.
    specialize (INB1 ltac:(lia) ltac:(lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS; cbn [rin_ivs fst snd];
                 split; [lia|]; split; [lia|]; intros X; apply CI_W_RANGE in X; unfold DC_CTX in X; lia)).
    assert (R201 := cfr_cells_static _ _ _ _ _ _ _ _ CFR1 R20). cbn [cells_size csize Nat.add] in R201.
    specialize (R201 ltac:(lia) ltac:(lia) ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS; cbn [rin_ivs fst snd];
                 split; [lia|]; split; [lia|]; intros X; apply CI_W_RANGE in X; unfold DC_CTX in X; lia)).
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
    rewrite unsigned_lit in ST1 by lia.
    pose proof RK as (LK0 & _ & _ & LKC & LKIMG). unfold mutex_cells in MC. unfold DC_GLOBAL_LOCK in GLK.
    pose proof (munch_refl [(3333808, 3333809); (3333828, 0x32dec8)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    (* [comment removed for export] *)
    cprefix. step. th_if_lit. step. cstep. cstep. do 3 step.
    lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into STe end.
    lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -32) _ |- _ => release_frame H STe (bv_unsigned sp) end.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
    lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
    lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
    assert (CRESf : CI_RES pk LBall1 L1 mf).
    { eapply (CI_RES_cfr pk LBall1 L1 m1 mf (bv_unsigned sp)); [exact CRES|].
      refine (proj1 (cframe_seg (fun q => q = pk) FXI_AW (bv_unsigned sp) st1 LBall1 L1 m1 st1 LBall1 L1 m1 _ mf (cframe_refl _ _ _ _ _ _ _) MU1 WM1 HP1 ltac:(lia) _)).
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold FXI_AW, DC_S, RATP; cbn [rin_ivs fst snd]; lia]|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold FXI_AW, DC_S, RATP; cbn [rin_ivs fst snd]; lia]| apply Forall_nil]. }
    chere. apply climpl_done.
    eexists. exists mf, LBall1.
    split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [exact GR1|].
    split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
      - apply Forall_cons; [apply cwin_bss; lia|]. apply Forall_cons; [apply cwin_bss; lia| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    split. { eapply cframe_seg; [eapply cframe_call; [exact FRa| exact FRM1| lia| intros a X; unfold DCDI_W; cbn [rin_ivs]; right; right; exact X| intros q _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold DCDI_W, DC_S; cbn [rin_ivs fst snd]; left; lia]|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold DCDI_W, DC_S; cbn [rin_ivs fst snd]; right; left; lia]| apply Forall_nil]. }
    split. { exists pk, LK. split; [exact INK|]. split; [exact RK|]. split; [unfold mutex_cells; eassumption|]. split; [unfold DC_GLOBAL_LOCK; eassumption|]. split; [exact FRESH| exact CRESf]. }
    change (3333808 + 20) with 3333828. split; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition GDC_STACK : Z := 32 + 128 + 32 + CI_STK.
  Definition GDC_W : list (Z * Z) := (DC_S, DC_S + 24) :: (0x351c90, 0x351c9c) :: (0x351890 + 8 * 3, 0x351890 + 8 * 3 + 8) :: (RATP + -96, RATP + -80) :: CI_W.
  Definition gdc_res (oldcb sh : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
    fun v LBall' L' m' => v = Z_to_bv 64 DC_CTX
      /\ (exists (pk : bptr) (LK : Z), In (pk, LK, 40) LBall' /\ rblock_range LK 40 /\ rw_cells usegs m' LK (mutex_cells z64 z64)
            /\ rw_cells usegs m' DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> q <> pk)
            /\ CI_RES pk LBall' L' m')
      /\ rw_cells usegs m' DC_S [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' (DC_S + 4) [C4 (Z_to_bv 64 3)]
      /\ rw_cells usegs m' (DC_S + 8) [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' (DC_S + 12) [C4 (Z_to_bv 64 1)]
      /\ rw_cells usegs m' (DC_S + 16) [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' (DC_S + 20) [C4 (Z_to_bv 64 1)]
      /\ rw_cells usegs m' (RATP + -96) [C8 oldcb] /\ rw_cells usegs m' (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)]
      /\ rw_cells usegs m' 0x351c90 [C4 (Z_to_bv 64 3)] /\ rw_cells usegs m' 0x351c98 [C4 z64; C4 z64; C4 sh]
      /\ rw_cells usegs m' (0x351890 + 8 * 3) [C8 (Z_to_bv 64 0x2bdf1c)] /\ rw_cells usegs m' (0x351cd0 + 8 * 3) [C8 z64].

  Definition gdc_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z) (kold r12 r20 oldcb sh w : word),
    (CI_EV <= f)%nat -> croom L CI_A CI_B CI_BIG -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - GDC_STACK -> bv_unsigned sp mod 16 = 0 ->
    rw_cells usegs m DC_S [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (DC_S + 4) [C4 kold] -> rw_cells usegs m (DC_S + 8) [C4 z64] -> rw_cells usegs m (DC_S + 12) [C4 r12] ->
    rw_cells usegs m (DC_S + 16) [C4 z64] -> rw_cells usegs m (DC_S + 20) [C4 r20] -> ctx0 m ->
    rw_cells usegs m (RATP + -96) [C8 oldcb] -> rw_cells usegs m (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)] ->
    rw_cells usegs m 0x351c90 [C4 (Z_to_bv 64 2)] -> rw_cells usegs m 0x351c98 [C4 z64; C4 z64; C4 sh] ->
    rw_cells usegs m (0x351890 + 8 * 3) [C8 z64] -> rw_cells usegs m (0x351890 + 8 * 2) [C8 w] -> bv_unsigned w <> 0 -> rw_cells usegs m (0x351cd0 + 8 * 3) [C8 z64] ->
    CI_PRE LBall L m ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe485c) fc None m (seg_rom usegs))
           (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) GDC_W CI_EV CI_A CI_B CI_BIG (gdc_res oldcb sh LBall L)).

  (* [comment removed for export] *)
  Ltac cst_staticW CFR H Hn :=
    assert (Hn := cfr_cells_static _ _ _ _ _ _ _ _ CFR H);
    cbn [cells_size csize Nat.add] in Hn;
    specialize (Hn ltac:(lia) ltac:(lia));
    specialize (Hn ltac:(intros a Ha; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS;
                         split; [lia|]; split; [lia|]; cbn [rin_ivs fst snd]; intros [X|[X|X]]; [lia| lia| apply CI_W_RANGE in X; unfold DC_CTX in X; lia])).

  Theorem gdc_spec : gdc_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd kold r12 r20 oldcb sh w
           Hf ROOM CST SLO SP16 INB KC C8c R12 C16 R20 C0 CBC TSD NK KL KY3 KY2 WNZ SL3 CIP.
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    subst tp.
    unfold GDC_STACK, DC_S, GLOBALS_TOP, RATP in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
    change (3333808 + 4) with 3333812 in KC. change (3333808 + 8) with 3333816 in C8c. change (3333808 + 12) with 3333820 in R12.
    change (3333808 + 16) with 3333824 in C16. change (3333808 + 20) with 3333828 in R20.
    destruct (rheap_ssp _ _ _ HP) as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU.
    destruct C0 as [cbs C0]. unfold DC_CTX, CTX_SIZE in C0.
    pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (3333812, 3333832); (0x351c90, 0x351c9c); (0x351890 + 8 * 3, 0x351890 + 8 * 3 + 8); (3344744 + -96, 3344744 + -80)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    cprefix. step. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 3 step. step. do 5 step. step.
    pose proof T_run_once_enter_proof as OE. unfold T_run_once_enter_stmt, ssp_cells, got_ssp, ssp_guard in OE.
    tcall (OE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0xe47d0 oldcb rr_guard).
    all: try first [eassumption | reflexivity | lia | split; eassumption].
    clear OE. cbv beta delta [mkR]. try th_ret_lit. try cret_lit.
    unfold ONCE_RET_INIT, RUN_ONCE_RET, once_full_cells, ONCE_UNDO, ONCE_RET_FULL in *.
    pose proof dctki_proof as DK. unfold dctki_stmt, DC_S, RATP in DK.
    tcall (DK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo kold r12 sh w).
    all: try first [eassumption | reflexivity | lia].
    all: try (lazymatch goal with |- ro_cells usegs ?mm (3479696 + 8 * 2) _ => lazymatch goal with H : rw_cells usegs mm (3479696 + 8 * 2) _ |- _ => exact (proj1 H) end end).
    clear DK. cbv beta delta [mkR]. try th_ret_lit.
    change (3333808 + 4) with 3333812 in *. change (3333808 + 12) with 3333820 in *.
    (* [comment removed for export] *)
    pose proof (T_run_once_leave_proof) as OL. unfold T_run_once_leave_stmt, ssp_cells, got_ssp, ssp_guard, ONCE_RET_INIT, once_full_cells, ONCE_UNDO, ONCE_RET_FULL, RUN_ONCE_RET in OL.
    tcall (OL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -32) 3333816).
    all: try first [eassumption | reflexivity | lia | split; eassumption].
    clear OL. cbv beta delta [mkR]. try th_ret_lit. try cret_lit.
    step. step. step. th_if_lit. step. step. th_if_lit.
    step. do 2 step. step.
    pose proof T_run_once_enter_proof as OE. unfold T_run_once_enter_stmt, ssp_cells, got_ssp, ssp_guard in OE.
    tcall (OE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 0xe4814 oldcb rr_guard).
    all: try first [eassumption | reflexivity | lia | split; eassumption].
    clear OE. cbv beta delta [mkR]. try th_ret_lit. try cret_lit. chere.
    unfold ONCE_RET_INIT, RUN_ONCE_RET, once_full_cells, ONCE_UNDO, ONCE_RET_FULL in *.
    lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mi end.
    lazymatch goal with H : rw_cells usegs mi 3333824 _ |- _ => rename H into CC1 end.
    lazymatch goal with H : rw_cells usegs mi (3344744 + -96) _ |- _ => rename H into CB1 end.
    lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -32 + -128) _ |- _ => rename H into OF1 end.
    lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -32 + -32) _ |- _ => rename H into OF2 end.
    lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -32 + -16) _ |- _ => rename H into OF3 end.
    lazymatch goal with H : rw_cells usegs mi (bv_unsigned sp + -32) _ |- _ => rename H into FR0 end.
    lazymatch goal with H : rw_cells usegs mi 3333808 _ |- _ => rename H into INBi end.
    lazymatch goal with H : rw_cells usegs mi 3333828 _ |- _ => rename H into R20i end.
    lazymatch goal with H : rw_cells usegs mi 3333832 _ |- _ => rename H into C0i end.
    lazymatch goal with H : stk usegs mi _ _ |- _ => rename H into STi end.
    lazymatch goal with H : mem_inv usegs mi |- _ => rename H into MIi end.
    assert (CSTi : cstate s LBall LB L mi (Z_to_bv 64 (bv_unsigned sp + -32 + -128)) (Z_to_bv 64 3344744) lo Bd).
    { eapply (cstate_seg _ _ _ _ _ m mi _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIi| | lia| lia| | rewrite unsigned_lit by lia; exact STi| rewrite unsigned_lit by lia; lia].
      - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply cwin_bss; lia|].
        apply Forall_cons; [unfold cwin; cbn [fst snd]; lia|]. apply Forall_cons; [unfold cwin; cbn [fst snd]; lia|]. apply Forall_cons; [unfold cwin; cbn [fst snd]; lia| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    assert (FRa : cframe (fun _ => False) GDC_W (bv_unsigned sp) s LBall L m s LBall L mi).
    { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
      apply Forall_cons; [apply cseg_ok_stack; lia|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold GDC_W, DC_S; cbn [rin_ivs fst snd]; left; lia]|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold GDC_W, DC_S; cbn [rin_ivs fst snd]; right; left; lia]|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold GDC_W, DC_S; cbn [rin_ivs fst snd]; right; right; left; lia]|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold GDC_W, DC_S, RATP; cbn [rin_ivs fst snd]; right; right; right; left; lia]| apply Forall_nil]. }
    ci_pre_here CIP MU WM.
    eapply climpl_seq.
    { eapply dcdi_spec with (lo := lo) (B := Bd); [lia| exact ROOM| exact CSTi| rewrite unsigned_lit by lia; lia| rewrite ?unsigned_lit by lia; lia| exact INBi| exact R20i| eexists; exact C0i| assumption]. }
    intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & ((pk & LK & INK & RK & MC & GLK & FRESH & CRES) & INB1 & R201)).
    destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
    cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). unfold DCDI_W, DC_S in FRM1. unfold DC_S in INB1, R201. change (3333808 + 20) with 3333828 in R201.
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR0 ltac:(lia)) as FR1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OF1 ltac:(lia)) as OF1b.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OF2 ltac:(lia)) as OF2b.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OF3 ltac:(lia)) as OF3b.
    cst_staticW CFR1 CC1 CC2. cst_staticW CFR1 CB1 CB2.
    lazymatch goal with H : rw_cells usegs mi 3333816 _ |- _ => cst_staticW CFR1 H C81 end.
    lazymatch goal with H : rw_cells usegs mi 3333812 _ |- _ => cst_staticW CFR1 H KC1 end.
    lazymatch goal with H : rw_cells usegs mi 3333820 _ |- _ => cst_staticW CFR1 H R121 end.
    lazymatch goal with H : rw_cells usegs mi (3344744 + -88) _ |- _ => cst_staticW CFR1 H TSD1 end.
    lazymatch goal with H : rw_cells usegs mi 3480720 _ |- _ => cst_staticW CFR1 H NK1 end.
    lazymatch goal with H : rw_cells usegs mi 3480728 _ |- _ => cst_staticW CFR1 H KL1 end.
    lazymatch goal with H : rw_cells usegs mi (3479696 + 8 * 3) _ |- _ => cst_staticW CFR1 H KY31 end.
    lazymatch goal with H : rw_cells usegs mi (3479696 + 8 * 2) _ |- _ => cst_staticW CFR1 H KY21 end.
    lazymatch goal with H : rw_cells usegs mi (3480784 + 8 * 3) _ |- _ => cst_staticW CFR1 H SL31 end.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
    rewrite unsigned_lit in ST1 by lia.
    destruct (rheap_ssp _ _ _ HP1) as [GOT1 GU1]. unfold got_ssp, ssp_guard in GOT1, GU1.
    pose proof RK as (LK0 & _ & _ & LKC & LKIMG). unfold mutex_cells in MC. unfold DC_GLOBAL_LOCK in GLK.
    hide RK. hide FRESH.
    assert (FRM0 : cframe (fun _ => False) GDC_W (bv_unsigned sp) s LBall L m st1 LBall1 L1 m1).
    { eapply cframe_call; [exact FRa| exact FRM1| lia| | intros q _ X; exact X].
      intros a X. unfold GDC_W, DC_S, RATP. cbn [rin_ivs fst snd app] in X |- *. destruct X as [X|[X|X]]; [left; lia| left; lia| do 4 right; exact X]. }
    clear FRa CSTi CFR1 FRM1.
    pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp - 32); (3333824, 3333828); (3344744 + -96, 3344744 + -88)]%Z m1) as MU1.
    pose proof (wmono_refl usegs m1) as WM1.
    (* [comment removed for export] *)
    cprefix.
    pose proof (T_run_once_leave_proof) as OL. unfold T_run_once_leave_stmt, ssp_cells, got_ssp, ssp_guard, ONCE_RET_INIT, once_full_cells, ONCE_UNDO, ONCE_RET_FULL, RUN_ONCE_RET in OL.
    tcall (OL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -32) 3333824).
    all: try first [eassumption | reflexivity | lia | split; eassumption].
    clear OL. cbv beta delta [mkR]. try th_ret_lit. try cret_lit.
    step. step. step. th_if_lit. step. step. th_if_lit. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mk end.
    assert (KCr : ro_cells usegs mk 3333812 [C4 (Z_to_bv 64 3)]) by (lazymatch goal with H : rw_cells usegs mk 3333812 _ |- _ => exact (proj1 H) end).
    assert (TSDr : ro_cells usegs mk (3344744 + -88) [C8 (Z_to_bv 64 3480784)]) by (lazymatch goal with H : rw_cells usegs mk (3344744 + -88) _ |- _ => exact (proj1 H) end).
    assert (SLr : ro_cells usegs mk (3480784 + 8 * 3) [C8 z64]) by (lazymatch goal with H : rw_cells usegs mk (3480784 + 8 * 3) _ |- _ => exact (proj1 H) end).
    tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 3480784 3 z64).
    all: try first [eassumption | lia].
    clear KCr TSDr SLr. cbv beta delta [mkR]. try th_ret_lit.
    step. step. step. step. th_if_lit. step. do 3 step.
    lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into STe end.
    lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -32) _ |- _ => release_frame H STe (bv_unsigned sp) end.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
    lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
    lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
    unfold hideP in *.
    assert (CRESf : CI_RES pk LBall1 L1 mf).
    { eapply (CI_RES_cfr pk LBall1 L1 m1 mf (bv_unsigned sp)); [exact CRES|].
      refine (proj1 (cframe_seg (fun q => q = pk) FXI_AW (bv_unsigned sp) st1 LBall1 L1 m1 st1 LBall1 L1 m1 _ mf (cframe_refl _ _ _ _ _ _ _) MU1 WM1 HP1 ltac:(lia) _)).
      apply Forall_cons; [apply cseg_ok_stack; lia|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold FXI_AW, DC_S, RATP; cbn [rin_ivs fst snd]; lia]|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold FXI_AW, DC_S, RATP; cbn [rin_ivs fst snd]; lia]| apply Forall_nil]. }
    chere. apply climpl_done.
    eexists. exists mf, LBall1.
    split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [exact GR1|].
    split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
      - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply cwin_bss; lia|]. apply Forall_cons; [unfold cwin; cbn [fst snd]; lia| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    split. { eapply cframe_seg; [exact FRM0| exact MU1| exact WM1| exact HP1| lia|].
      apply Forall_cons; [apply cseg_ok_stack; lia|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold GDC_W, DC_S; cbn [rin_ivs fst snd]; left; lia]|].
      apply Forall_cons; [apply cseg_ok_static; [lia| lia| intros a Ha; unfold GDC_W, DC_S, RATP; cbn [rin_ivs fst snd]; do 3 right; left; lia]| apply Forall_nil]. }
    unfold gdc_res, DC_S, DC_GLOBAL_LOCK, RATP, mutex_cells. split; [reflexivity|].
    split. { exists pk, LK. repeat match goal with |- _ /\ _ => split end; try eassumption. }
    change (3333808 + 4) with 3333812. change (3333808 + 8) with 3333816. change (3333808 + 12) with 3333820. change (3333808 + 16) with 3333824. change (3333808 + 20) with 3333828.
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition gal_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (lo LK : Z),
    a0 = Z_to_bv 64 DC_GLOBAL_LOCK -> a1 = z64 -> a2 = z64 ->
    rw_cells usegs m DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] -> rw_cells usegs m LK (mutex_cells z64 z64) -> 0 < LK -> LK mod 16 = 0 -> LK + 40 <= alloc_ceiling ->
    (LK + 40 <= 0x10000 \/ 0x353000 <= LK) ->
    stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : mem),
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (DC_GLOBAL_LOCK + 8)) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
        /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (LK + 4, LK + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ stk usegs m' lo (bv_unsigned sp)
        /\ rw_cells usegs m' DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] /\ rw_cells usegs m' LK (mutex_cells z64 (Z_to_bv 64 16)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe5000) fc None m (seg_rom usegs)).

  Theorem gal_proof : gal_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros until LK. intros -> -> -> GLK MC LK0 LK16 LKC LKIMG ST LO SLO MI.
    unfold DC_GLOBAL_LOCK in *. unfold ceil_window in CEIL_RANGE__.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (LK + 4, LK + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold mutex_cells in MC.
    step. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 4 step. step. do 2 step. step. th_if_lit.
    step. step. step. th_if_lit. step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
    step. th_if_lit. step.
    pose proof T_write_lock_proof as WL. unfold T_lock_stmt, mutex_cells in WL.
    tcall (WL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
    all: try first [eassumption | lia].
    all: try (Z.div_mod_to_equations; lia).
    clear WL. cbv beta delta [mkR]. try th_ret_lit.
    step. th_if_lit. do 3 step. step. th_if_lit. do 2 step. do 4 step.
    lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into STe end.
    lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -32) _ |- _ => release_frame H STe (bv_unsigned sp) end.
    step. step.
    apply evt_done. do 5 eexists. eexists. split; [reflexivity|]. unfold mutex_cells. repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition FXI_STACK : Z := 48 + 16 + GDC_STACK.
  Definition fxi_res (oldcb sh : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
    fun _ LBall' L' m' =>
         (exists (pk : bptr) (LK : Z), In (pk, LK, 40) LBall' /\ rblock_range LK 40 /\ rw_cells usegs m' LK (mutex_cells z64 z64)
            /\ rw_cells usegs m' DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] /\ (forall q, In q (map blk_id LBall) \/ In q (map fst L) -> q <> pk)
            /\ CI_RES pk LBall' L' m')
      /\ rw_cells usegs m' DC_S [C1 (Z_to_bv 8 1)] /\ rw_cells usegs m' (DC_S + 4) [C4 (Z_to_bv 64 3)]
      /\ rw_cells usegs m' (DC_S + 8) [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' (DC_S + 12) [C4 (Z_to_bv 64 1)]
      /\ rw_cells usegs m' (DC_S + 16) [C4 (Z_to_bv 64 2)] /\ rw_cells usegs m' (DC_S + 20) [C4 (Z_to_bv 64 1)]
      /\ rw_cells usegs m' (RATP + -96) [C8 oldcb] /\ rw_cells usegs m' (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)]
      /\ rw_cells usegs m' 0x351c90 [C4 (Z_to_bv 64 3)] /\ rw_cells usegs m' 0x351c98 [C4 z64; C4 z64; C4 sh]
      /\ rw_cells usegs m' (0x351890 + 8 * 3) [C8 (Z_to_bv 64 0x2bdf1c)] /\ rw_cells usegs m' (0x351cd0 + 8 * 3) [C8 z64].

  Definition fxi_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z) (kold r12 r20 oldcb sh w : word),
    (CI_EV <= f)%nat -> croom L CI_A CI_B CI_BIG -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - FXI_STACK -> bv_unsigned sp mod 16 = 0 ->
    a0 = z64 -> a1 = Z_to_bv 64 (-1) ->
    rw_cells usegs m DC_S [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (DC_S + 4) [C4 kold] -> rw_cells usegs m (DC_S + 8) [C4 z64] -> rw_cells usegs m (DC_S + 12) [C4 r12] ->
    rw_cells usegs m (DC_S + 16) [C4 z64] -> rw_cells usegs m (DC_S + 20) [C4 r20] -> ctx0 m ->
    rw_cells usegs m (RATP + -96) [C8 oldcb] -> rw_cells usegs m (RATP + -88) [C8 (Z_to_bv 64 0x351cd0)] ->
    rw_cells usegs m 0x351c90 [C4 (Z_to_bv 64 2)] -> rw_cells usegs m 0x351c98 [C4 z64; C4 z64; C4 sh] ->
    rw_cells usegs m (0x351890 + 8 * 3) [C8 z64] -> rw_cells usegs m (0x351890 + 8 * 2) [C8 w] -> bv_unsigned w <> 0 -> rw_cells usegs m (0x351cd0 + 8 * 3) [C8 z64] ->
    CI_PRE LBall L m ->
    climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe5120) fc None m (seg_rom usegs))
           (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) GDC_W CI_EV CI_A CI_B CI_BIG (fxi_res oldcb sh LBall L)).

  Theorem fxi_spec : fxi_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f lo Bd kold r12 r20 oldcb sh w
           Hf ROOM CST SLO SP16 -> -> INB KC C8c R12 C16 R20 C0 CBC TSD NK KL KY3 KY2 WNZ SL3 CIP.
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    subst tp.
    unfold FXI_STACK, GDC_STACK, DC_S, GLOBALS_TOP, RATP in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj INB (conj KC (conj C8c (conj R12 (conj C16 (conj R20 (conj C0 (conj CBC (conj TSD (conj NK (conj KL (conj KY3 (conj KY2 SL3))))))))))))) as CELLS.
    clear INB KC C8c R12 C16 R20 C0 CBC TSD NK KL KY3 KY2 SL3.
    (* [comment removed for export] *)
    cprefix. step. th_frame 16%nat [8; 8]%nat ST. do 2 step. step. do 3 step. do 2 step.
    lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into ST0 end.
    lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -16) _ |- _ => release_frame H ST0 (bv_unsigned sp) end.
    step. step.
    step. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST0. do 5 step. step. do 2 step. step.
    step. th_if_lit. step. lazymatch goal with H : stk usegs _ lo _ |- _ => th_frame 16%nat [8; 8]%nat H end. cstep. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (TR : forall A cs, rw_cells usegs m A cs -> A + Z.of_nat (cells_size cs) <= 3485696 -> rw_cells usegs mm A cs)
        by (intros A cs H HB; eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from]; lia]) end.
    destruct CELLS as (INB & KC & C8c & R12 & C16 & R20 & C0 & CBC & TSD & NK & KL & KY3 & KY2 & SL3).
    apply TR in INB; [| cbn; lia]. apply TR in KC; [| cbn; lia]. apply TR in C8c; [| cbn; lia]. apply TR in R12; [| cbn; lia]. apply TR in C16; [| cbn; lia].
    apply TR in R20; [| cbn; lia]. destruct C0 as [cbs C0]. unfold DC_CTX, CTX_SIZE in C0. apply TR in C0; [| cbn; lia]. apply TR in CBC; [| cbn; lia]. apply TR in TSD; [| cbn; lia].
    apply TR in NK; [| cbn; lia]. apply TR in KL; [| cbn; lia]. apply TR in KY3; [| cbn; lia]. apply TR in KY2; [| cbn; lia]. apply TR in SL3; [| cbn; lia].
    clear TR.
    chere.
    lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into ma end.
    lazymatch goal with H : stk _ ma _ _ |- _ => rename H into STa end.
    lazymatch goal with H : mem_inv _ ma |- _ => rename H into MIa end.
    lazymatch goal with H : rw_cells usegs ma (bv_unsigned sp + -48) _ |- _ => rename H into FRA end.
    lazymatch goal with H : rw_cells usegs ma (bv_unsigned sp + -64) _ |- _ => rename H into FRB end.
    assert (CSTa : cstate s LBall LB L ma (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 3344744) lo Bd).
    { eapply (cstate_seg _ _ _ _ _ m ma _ _ _ lo Bd (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIa| | lia| lia| | rewrite unsigned_lit by lia; exact STa| rewrite unsigned_lit by lia; lia].
      - constructor; [apply cwin_stack; lia| constructor].
      - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    assert (FRa : cframe (fun _ => False) GDC_W (bv_unsigned sp) s LBall L m s LBall L ma).
    { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
    ci_pre_here CIP MU WM.
    eapply climpl_seq.
    { eapply gdc_spec with (lo := lo) (B := Bd); [lia| exact ROOM| exact CSTa| rewrite unsigned_lit by lia; unfold GDC_STACK; lia| rewrite ?unsigned_lit by lia; lia
        | exact INB| exact KC| exact C8c| exact R12| exact C16| exact R20| eexists; exact C0| exact CBC| exact TSD| exact NK| exact KL| exact KY3| exact KY2| exact WNZ| exact SL3| assumption]. }
    intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & GRES).
    destruct GRES as (-> & (pk & LK & INK & RK & MC & GLK & FRESH & CRES) & INB1 & KC1 & C81 & R121 & C161 & R201 & CBC1 & TSD1 & NK1 & KL1 & KY31 & SL31).
    destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
    cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia). unfold GDC_W, DC_S, RATP in FRM1. unfold DC_S in INB1, KC1, C81, R121, C161, R201. unfold RATP in CBC1, TSD1.
    unfold DC_GLOBAL_LOCK in GLK. unfold DC_CTX.
    change (3333808 + 4) with 3333812 in KC1. change (3333808 + 8) with 3333816 in C81. change (3333808 + 12) with 3333820 in R121. change (3333808 + 16) with 3333824 in C161. change (3333808 + 20) with 3333828 in R201.
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRA ltac:(lia)) as FRA1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRB ltac:(lia)) as FRB1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
    rewrite unsigned_lit in ST1 by lia.
    pose proof RK as (LK0 & LK16 & _ & LKC & LKIMG). hide RK. hide FRESH. unfold mutex_cells in MC.
    assert (FRM0 : cframe (fun _ => False) GDC_W (bv_unsigned sp) s LBall L m st1 LBall1 L1 m1).
    { eapply cframe_call; [exact FRa| exact FRM1| lia| intros a X; unfold GDC_W, DC_S, RATP; exact X| intros q _ X; exact X]. }
    clear FRa CSTa CFR1 FRM1.
    pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp - 48); (LK + 4, LK + 8)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    (* [comment removed for export] *)
    cprefix. do 2 step.
    lazymatch goal with H : stk usegs _ lo _ |- _ => release_frame FRB1 H (bv_unsigned sp + -48) end.
    step. step. th_if_lit. step. step. th_if_lit. do 2 step.
    step. th_if_lit. do 3 step. step.
    pose proof gal_proof as GAL. unfold gal_stmt, DC_GLOBAL_LOCK, mutex_cells in GAL.
    tcall (GAL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo LK).
    all: try first [eassumption | reflexivity | lia].
    clear GAL. cbv beta delta [mkR]. try th_ret_lit.
    step. th_if_lit. step. th_if_lit. step. step. step. th_if_lit. step. step.
    pose proof T_unlock_proof as UL. unfold T_unlock_stmt, mutex_cells in UL.
    tcall (UL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
    all: try first [eassumption | lia].
    all: try (Z.div_mod_to_equations; lia).
    clear UL. cbv beta delta [mkR]. try th_ret_lit.
    step. do 5 step.
    lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into STe end.
    lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -48) _ |- _ => release_frame H STe (bv_unsigned sp) end.
    step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
    lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end.
    lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
    unfold hideP in *.
    assert (CRESf : CI_RES pk LBall1 L1 mf).
    { eapply (CI_RES_cfr pk LBall1 L1 m1 mf (bv_unsigned sp)); [exact CRES|].
      refine (proj1 (cframe_seg (fun q => q = pk) FXI_AW (bv_unsigned sp) st1 LBall1 L1 m1 st1 LBall1 L1 m1 _ mf (cframe_refl _ _ _ _ _ _ _) MU1 WM1 HP1 ltac:(lia) _)).
      apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
      apply (cseg_ok_block _ _ _ _ _ (pk, LK, 40)); [exact INK| intros b0 _ NT; exact NT| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia. }
    chere. apply climpl_done.
    eexists. exists mf, LBall1.
    split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [exact GR1|].
    split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| exact SPB| | exact STf| exact SPB].
      - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
        apply (cwin_block _ _ _ (pk, LK, 40)); [exact INK| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    split. { eapply cframe_seg; [exact FRM0| exact MU1| exact WM1| exact HP1| lia|].
      apply Forall_cons; [apply cseg_ok_stack; lia|]. apply Forall_cons; [| apply Forall_nil].
      apply (cseg_ok_block _ _ _ _ _ (pk, LK, 40)); [exact INK| | |]; [| unfold blk_addr, blk_size; cbn [fst snd]; lia..].
      intros b0 Hb0 _ E1. apply (FRESH (blk_id b0)); [left; apply in_map; exact Hb0| cbn [blk_id fst] in E1; exact E1]. }
    unfold fxi_res, DC_S, DC_GLOBAL_LOCK, RATP, mutex_cells.
    split. { exists pk, LK. unfold hideP in RK. repeat match goal with |- _ /\ _ => split end; try eassumption. }
    change (3333808 + 4) with 3333812. change (3333808 + 8) with 3333816. change (3333808 + 12) with 3333820. change (3333808 + 16) with 3333824. change (3333808 + 20) with 3333828.
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.
End CtxInit.
End WithCeiling0.
