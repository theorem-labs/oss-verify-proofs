(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Startup_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl F_printf_iface Stdio_iface Stdio_init F_printf_diag RDriver_kit RDriver_ctx.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_atexit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_fuzz_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs F_memset F_memcpy F_strlen.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ua := idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma u64ro_read : forall m A ws (i : Z) w a,
  bytes_at rsegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
  ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Definition CJ0 (mm : mem) : Prop :=
  rw_cells rsegs mm 0x3b6d0 [C1 (Z_to_bv 8 0)]
  /\ rw_cells rsegs mm 0x3b6e0 [CB 16 (repeat (Z_to_bv 8 0) 16)]
  /\ rw_cells rsegs mm 0x2a108 [C8 (Z_to_bv 64 0)]
  /\ GD mm
  /\ atx_state false mm.

Definition cj0_addr (a : Z) : Prop :=
  (0x3b6d0 <= a < 0x3b6d1) \/ (0x3b6e0 <= a < 0x3b6f0) \/ (0x2a108 <= a < 0x2a128)
  \/ (0x2b1a8 <= a < 0x2b478) \/ (0x3b700 <= a < 0x3b70c).

Definition cj0x_addr (a : Z) : Prop := cj0_addr a \/ atx_state_addr a.

Lemma gd_bytes_len : Forall (fun r => Z.of_nat (length (gd_bytes (fst r) (snd r))) = Z.of_nat (snd r)) GD_ranges.
Proof. unfold GD_ranges. repeat (apply Forall_cons; [vm_compute; reflexivity|]). apply Forall_nil. Qed.

Lemma GD_agree : forall (P : Z -> Prop) m m', agree_on rsegs P m m' ->
  (forall a, (0x2b1a8 <= a < 0x2b478) \/ (0x3b700 <= a < 0x3b70c) \/ (0x2a118 <= a < 0x2a128) -> P a) -> GD m -> GD m'.
Proof.
  intros P m m' AG HP G. unfold GD in *. apply Forall_forall. intros r Hr.
  pose proof (proj1 (Forall_forall _ _) G r Hr) as B. pose proof (proj1 (Forall_forall _ _) gd_bytes_len r Hr) as L.
  eapply bytes_at_agree; [exact AG| exact B|]. intros x Hx. rewrite L in Hx. apply HP.
  unfold GD_ranges in Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd Z.of_nat Pos.of_succ_nat] in Hx; lia.
Qed.

Lemma CJ0_agree : forall (P : Z -> Prop) m m', agree_on rsegs P m m' -> (forall a, cj0x_addr a -> P a) -> CJ0 m -> CJ0 m'.
Proof.
  intros P m m' AG HP (A1 & A2 & A3 & A4 & A5). unfold CJ0 in *.
  Ltac trc AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; apply HP; left; unfold cj0_addr; cbn in Ha; lia].
  split; [trc AG HP A1|]. split; [trc AG HP A2|]. split; [trc AG HP A3|].
  split; [eapply GD_agree; [exact AG| | exact A4]; intros a Ha; apply HP; left; unfold cj0_addr; lia|].
  eapply atx_state_agree; [exact AG| intros a Ha; apply HP; right; exact Ha| exact A5].
Qed.
Lemma CJ0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> CJ0 m -> CJ0 m'.
Proof.
  intros LB SP m m' HP. apply (CJ0_agree _ _ _ HP). intros a Ha. right; left.
  unfold cj0x_addr, cj0_addr, atx_state_addr, atx_addr, RAEF_INCB, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
Qed.
Lemma CJ0_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> (forall a, cj0x_addr a -> outside W a) -> CJ0 m -> CJ0 m'.
Proof. intros W m m' MU WM HW. apply (CJ0_agree _ _ _ (agree_on_of_munch rsegs _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

Section A.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis HT : 0 < TID < 4194304.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).

  Definition BASE (mm : mem) : Prop :=
    stk rsegs mm LO' (usp0 + -128) /\ mem_inv rsegs mm /\ RSTAT TID mm /\ rauxv_ok mm usp0 /\ bytes_at rsegs mm usp0 IMGB
    /\ stderr_wfile0 mm /\ stdout_file mm stdout_init /\ stk rsegs mm RSV (RSV + 65536).

  #[using="VSP VARGV VENVP"] Lemma IMGB_len : usp0 + Z.of_nat (length IMGB) <= 2^64.
  Proof.
    destruct VSP as (A & B & C). unfold sp_window_lo, sp_window_hi in *.
    pose proof (build_stack_bytes_length rph sp0 argv envp uid hw rnd). pose proof (raw_len_nonneg rph sp0 argv envp uid hw rnd).
    destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _). unfold raw_len, struct_size, argc, envc in *. lia.
  Qed.

  #[using="ESF"] Lemma IMGB_len47 : usp0 + Z.of_nat (length IMGB) <= 2^47.
  Proof.
    pose proof (build_stack_bytes_within_span rph sp0 argv envp uid hw rnd). unfold entry_stack_fits, sp_window_hi in ESF. lia.
  Qed.

  #[using="Type"] Lemma BASE_heap_pres : forall LB m m', BASE m -> rheap_pres LB (usp0 + -128) m m' ->
    mem_inv rsegs m' -> stk rsegs m' LO' (usp0 + -128) -> rauxv_ok m' usp0 -> BASE m'.
  Proof.
    intros LB m m' (ST & MI & RS & AUX & IMG & SE & SO & RSS) HP MI' ST' AUX'.
    split; [exact ST'|]. split; [exact MI'|]. split; [eapply RSTAT_heap_pres; [exact HP| exact RS]|]. split; [exact AUX'|].
    split; [eapply rheap_pres_bytes_at; [exact HP| exact IMG| left; lia]|].
    split; [eapply stderr_wfile0_heap_pres; [exact HP| exact SE]|]. split; [eapply stdout_file_heap_pres; [exact HP| exact SO]|].
    eapply stk_agree; [exact HP| exact RSS|]. intros a Ha. right; left.
    unfold RSV, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. lia.
  Qed.

  Definition WOK (iv : Z * Z) : Prop :=
    (LO' <= fst iv /\ snd iv <= usp0 + -128) \/ (fst iv = RERRNO /\ snd iv = RERRNO + 4)
    \/ (snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x5d000 <= fst iv)).

  Definition WOKR (iv : Z * Z) : Prop := WOK iv \/ (RSV <= fst iv /\ snd iv <= RSV + 65536).

  #[using="Type"] Lemma WOK_WOKR : forall W, Forall WOK W -> Forall WOKR W.
  Proof. intros W H. eapply Forall_impl; [| exact H]. intros iv Hiv. left. exact Hiv. Qed.

  #[using="VSP CEIL"] Lemma WOKR_outside : forall W a, Forall WOKR W ->
    (usp0 + -128 <= a \/ (0x10000 <= a < 0x5d000 /\ ~ (RERRNO <= a < RERRNO + 4) /\ ~ (RSV <= a < RSV + 65536))) -> outside W a.
  Proof.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOKR, WOK, LO, RERRNO, RSV in H1. cbn [fst snd] in H1. unfold RERRNO, RSV in Ha. lia.
  Qed.

  #[using="VSP CEIL"] Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp0 + -128 <= a \/ (0x10000 <= a < 0x5d000 /\ ~ (RERRNO <= a < RERRNO + 4))) -> outside W a.
  Proof.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOK, LO, RERRNO in H1. cbn [fst snd] in H1. unfold RERRNO in Ha. lia.
  Qed.

  #[using="VSP CEIL VARGV VENVP"] Lemma BASE_munchR : forall W m m', BASE m -> Forall WOKR W -> munch W m m' -> wmono rsegs m m' ->
    mem_inv rsegs m' -> stk rsegs m' LO' (usp0 + -128) -> stk rsegs m' RSV (RSV + 65536) -> BASE m'.
  Proof.
    intros W m m' (ST & MI & RS & AUX & IMG & SE & SO & RSS) HW MU WM MI' ST' RSS'. pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof IMGB_len as IL. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply RSTAT_munch; [exact MU| exact WM| intros a Ha; apply WOKR_outside; [exact HW| unfold rstat_addr, RERRNO, RSV in *; lia]| exact RS]|].
    split.
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      eapply Forall_impl; [| exact HW]. intros [lo1 hi1] H. unfold WOKR, WOK, RERRNO, RAUXV_CELL, RLIBC, LO, RSV in *. cbn [fst snd] in *. lia. }
    split.
    { eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact IMG|]. intros a Ha. cbn. apply WOKR_outside; [exact HW| left; lia]. }
    split; [| split; [| exact RSS']].
    - eapply stderr_wfile0_munch; [exact MU| exact WM| | exact SE]. intros a Ha. apply WOKR_outside; [exact HW| unfold stderr_addr, RERRNO, RSV in *; lia].
    - eapply stdout_file_munch; [exact MU| exact WM| | exact SO]. intros a Ha. apply WOKR_outside; [exact HW| unfold stdout_addr, RERRNO, RSV in *; lia].
  Qed.

  #[using="VSP CEIL VARGV VENVP"] Lemma BASE_munch : forall W m m', BASE m -> Forall WOK W -> munch W m m' -> wmono rsegs m m' ->
    mem_inv rsegs m' -> stk rsegs m' LO' (usp0 + -128) -> BASE m'.
  Proof.
    intros W m m' BA HW MU WM MI' ST'. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *.
    eapply BASE_munchR; [exact BA| apply WOK_WOKR; exact HW| exact MU| exact WM| exact MI'| exact ST'|].
    destruct BA as (_ & _ & _ & _ & _ & _ & _ & RSS).
    eapply stk_transport_disjoint; [exact RSS| exact MU| exact WM|].
    clear - HW SF. unfold RSV. induction W as [|[lo1 hi1] W IH]; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; exact H2].
    unfold WOK, LO, RERRNO in H1. cbn [fst snd] in H1. lia.
  Qed.

  #[using="VSP CEIL"] Lemma CJ0_munchWR : forall W m m', Forall WOKR W -> munch W m m' -> wmono rsegs m m' -> CJ0 m -> CJ0 m'.
  Proof.
    intros W m m' HW MU WM. apply (CJ0_munch _ _ _ MU WM). intros a Ha. apply WOKR_outside; [exact HW| unfold cj0x_addr, cj0_addr, atx_state_addr, atx_addr, RAEF_INCB, RERRNO, RSV in *; lia].
  Qed.
  #[using="VSP CEIL"] Lemma CJ0_munchW : forall W m m', Forall WOK W -> munch W m m' -> wmono rsegs m m' -> CJ0 m -> CJ0 m'.
  Proof. intros W m m' HW. apply CJ0_munchWR. apply WOK_WOKR. exact HW. Qed.

  #[using="VSP CEIL"] Lemma RHEAP_munchWR : forall s LB W m m', Forall WOKR W -> munch W m m' -> wmono rsegs m m' ->
    (forall iv, In iv W -> snd iv <= alloc_ceiling -> (snd iv <= 0x10000 \/ 0x5d000 <= fst iv) ->
                exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ->
    RHEAP s LB m -> RHEAP s LB m'.
  Proof.
    intros s LB W m m' HW MU WM HB HP. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *.
    eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
    apply Forall_forall. intros [lo1 hi1] Hin. pose proof (proj1 (Forall_forall _ _) HW _ Hin) as H.
    unfold WOKR, WOK, rclient_write_ok, RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK, LO, RSV in *. cbn [fst snd] in *.
    destruct H as [[H|[H|H]]|H]; [left; lia| right; left; lia| right; right| right; left; lia]. apply (HB (lo1, hi1)); [exact Hin| cbn; lia| cbn; lia].
  Qed.
  #[using="VSP CEIL"] Lemma RHEAP_munchW : forall s LB W m m', Forall WOK W -> munch W m m' -> wmono rsegs m m' ->
    (forall iv, In iv W -> snd iv <= alloc_ceiling -> (snd iv <= 0x10000 \/ 0x5d000 <= fst iv) ->
                exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ->
    RHEAP s LB m -> RHEAP s LB m'.
  Proof. intros s LB W m m' HW. apply RHEAP_munchWR. apply WOK_WOKR. exact HW. Qed.

  #[using="HCEIL VSP CEIL"] Lemma main_prologue : forall (Q : machine_state -> Prop) (ra s0 s1 a0 a1 a2 s2 s3 t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk rsegs m LO' (usp0 + -48) -> mem_inv rsegs m ->
    (forall m' (pad : list byte), rw_cells rsegs m' (usp0 + -128) [CB 8 pad; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs m' LO' (usp0 + -128) ->
        munch [(usp0 - 128, usp0 - 48)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        evt rsegs Q (MS (mkR ra (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x13b48) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (usp0 + -48)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x13b1c) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI K. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *.
    pose proof (munch_refl [(usp0 - 128, usp0 - 48)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. carve_frame 80%nat ST.
    do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end; [exact FR| exact ST| exact MU| exact WM| assumption].
  Qed.

  Definition P1 (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem) (pad : list byte),
      ms = MS (mkR (Z_to_bv 64 0x178b4) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                   (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                   (Z_to_bv 64 0x13b1c) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              bvmap_empty (Z_to_bv 64 0x13b4c) fc None mm (seg_rom rsegs)
      /\ MFRAME sp0 argv mm pad s7 s6 s5 s4 /\ BASE mm /\ RHEAP (ps_init (reservedZ rsegs) alloc_ceiling) [] mm /\ CJ0 mm
      /\ rw_cells rsegs mm RERRNO [C4 (Z_to_bv 64 0)] /\ frm0 fc.
End A.

Section A2.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis GW : guard_word = entry_guard rnd.
  Hypothesis GS : secret_word = entry_secret rnd.
  Hypothesis AUXINIT : rauxv_init_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis EXK : exit_k_stmt.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).

  #[using="VSP CEIL VARGV VENVP GW GS AUXINIT"] Lemma main_to_test : forall (ms : machine_state) (Q : machine_state -> Prop),
    rat_main sp0 argv envp uid hw rnd ms ->
    (forall (TID : Z) (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mm : mem) (pad : list byte),
        0 < TID < 4194304 ->
        MFRAME sp0 argv mm pad s7 s6 s5 s4 -> BASE sp0 argv envp uid hw rnd TID mm -> RHEAP (ps_init (reservedZ rsegs) alloc_ceiling) [] mm -> CJ0 mm ->
        rw_cells rsegs mm RERRNO [C4 (Z_to_bv 64 0)] ->
        evt rsegs Q (MS (mkR (Z_to_bv 64 0x178b4) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                          (Z_to_bv 64 2) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                          (Z_to_bv 64 0x13b1c) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        bvmap_empty (Z_to_bv 64 0x13b48) (Z_to_bv 32 0) None mm (seg_rom rsegs))) ->
    evt rsegs Q ms.
  Proof.
    intros ms Q AM K.
    destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & t & P0 & pg & m
                    & -> & MI & ST & TD & ERR & TLS & LIBC1 & LIBC2 & MTLS & SYSI & PROG & HWCAP & ENV & DSS & GUARD & GOT0 & GOTM & GCX & G28 & G38 & G50 & GOTG & GF & IA & FA & GD0 & INI & FIN & EXL & SOU & SEU & SIN & OFL & SOF & SEF & IMG & IMGW & HP0 & NONE & HT).
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. unfold LO in *.
    pose proof (bytes_at_bound _ _ _ _ IMG) as IMGBD.
    rewrite <- GW in GUARD.
    pose proof (heap_init sp0 argv envp m NONE LIBC1 LIBC2 GOTG GUARD MI) as [HP0i AUXC].
    pose proof (AUXINIT sp0 argv envp uid hw rnd m NONE LIBC1 LIBC2 GOTG GUARD MI IMG ltac:(unfold sp_window_lo; lia) ltac:(lia) GS) as AI.
    pose proof (tr_initialized_init m NONE) as C1. pose proof (tr_empty_init m NONE) as C2. pose proof (got_fuzzinit_init m NONE) as C3. pose proof (gd_init m NONE) as C4.
    pose proof (rstatx0_init m NONE) as [DSO0 AXS0]. pose proof (atx_state0_init m NONE) as AXF0. pose proof (rs_init m NONE) as RS0.
    pose proof (stderr_wfile0_init m ltac:(intros a Ha; apply NONE; [cbn in Ha |- *; lia| unfold rcrt_written in *; cbn in Ha |- *; lia])) as SE.

    clear TLS MTLS SYSI PROG HWCAP ENV DSS GOT0 GOTM G38 G50 IA INI IMGW HP0 NONE.
    replace (usp0 - 8388608) with (usp0 + -8388608) in ST by lia.
    eapply (main_prologue sp0 VSP CEIL); [unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST| exact MI|].
    intros m1 pad FR ST1 MU WM MI1. unfold LO in ST1.
    pose proof (agree_on_of_munch rsegs _ _ _ MU WM) as AG.
    assert (OUT : forall a, (a < usp0 - 128 \/ usp0 - 48 <= a) -> (fun a0 : Z => outside [(usp0 - 128, usp0 - 48)] a0) a) by (intros a Ha; cbn; lia).
    apply (K t t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1 pad HT).
    - exact FR.
    - split; [unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST1|]. split; [exact MI1|].
      split. { eapply (RSTAT_agree t _ _ _ AG); [intros a Ha; apply OUT; unfold rstat_addr in Ha; lia|].
               unfold RSTAT. split; [exact TD|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|]. split; [exact FIN|]. split; [exact GCX|].
               split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|]. split; [exact G28|]. split; [exact GD0|]. split; [exact DSO0 | exact AXS0]. }
      split. { eapply rauxv_ok_frame; [exact AI| exact MU| exact WM|]. constructor; [| constructor]. unfold RAUXV_CELL, RLIBC. cbn [fst snd]. lia. }
      split. { eapply bytes_at_agree; [exact AG| exact IMG| intros a Ha; apply OUT; lia]. }
      split. { eapply (stderr_wfile0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold stderr_addr in Ha; lia| exact SE]. }
      split. { eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT; unfold stdout_addr in Ha; lia| exact SOF]. }
      eapply (stk_agree rsegs _ _ _ _ _ AG); [exact RS0| intros a Ha; apply OUT; unfold RSV in Ha; lia].
    - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP0i| exact MU| exact WM|]. constructor; [| constructor]. left. cbn [fst snd]. lia.
    - eapply (CJ0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold cj0x_addr, cj0_addr, atx_state_addr, atx_addr, RAEF_INCB in Ha; lia|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4| exact AXF0].
    - eapply rw_cells_agree; [exact AG| unfold RERRNO; exact ERR| intros a Ha; apply OUT; cbn in Ha; unfold RERRNO in Ha; lia].
  Qed.

  #[using="VSP CEIL VARGV VENVP GW GS AUXINIT"] Lemma main_to_P1 : forall (arg0 arg1 : list byte) (ms : machine_state) (Q : machine_state -> Prop),
    argv = [arg0; arg1] -> rat_main sp0 argv envp uid hw rnd ms ->
    (forall TID ms', 0 < TID < 4194304 -> P1 sp0 argv envp uid hw rnd TID ms' -> evt rsegs Q ms') ->
    evt rsegs Q ms.
  Proof.
    intros arg0 arg1 ms Q EARGV AM K.
    eapply main_to_test; [exact AM|]. intros TID t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mm pad HT FR BA HP CJ ERR.
    unfold argc. rewrite EARGV. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- EARGV.
    pose proof BA as (ST & MI & _).
    zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    apply (K TID); [exact HT|].
    unfold P1. do 20 eexists. exists (Z_to_bv 32 0), mm, pad. split; [reflexivity|].
    split; [exact FR|]. split; [exact BA|]. split; [exact HP|]. split; [exact CJ|]. split; [exact ERR|]. vm_compute. reflexivity.
  Qed.

  #[using="HGW VSP CEIL VARGV VENVP ESF GW GS AUXINIT FPR EXK"] Lemma main_usage : forall ms (Q : at_parser -> PState -> machine_state -> Prop),
    rat_main sp0 argv envp uid hw rnd ms -> Z.of_nat (length argv) <> 2 ->
    implM rsegs (drv_pre (io_S ps_so set_so_ps) raw_malloc raw_free RSV (argv_Z argv))
          (ps_init (reservedZ rsegs) alloc_ceiling) Q ms.
  Proof.
    intros ms Q AM HARGC.
    unfold drv_pre. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length argv) =? 2) with false by (symmetry; apply Z.eqb_neq; exact HARGC). cbn [negb].
    eapply implM_evt with (P := fun ms' => implM rsegs
        (io_diag (io_S ps_so set_so_ps) (DUsage (nth 0 (argv_Z argv) []));;; exit_k (io_S ps_so set_so_ps) 2) (ps_init (reservedZ rsegs) alloc_ceiling) Q ms');
      [| intros ms' H; exact H].
    eapply main_to_test; [exact AM|]. intros TID t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mm pad HT FR BA HP CJ ERR.
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL.
    pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. unfold LO in *.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SO & RSS). unfold LO in ST.
    pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _ & _).
    destruct VARGV as (ARGC & _ & ARGLEN & NONUL & _).
    destruct argv as [|arg0 argv'] eqn:EARGV; [cbn in ARGC; lia|]. rewrite <- EARGV in *.

    destruct (argv_cstring sp0 argv envp uid hw rnd mm IMG 0 arg0 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
      as (p0 & slack0 & HP0 & P0LO & P0HI & STR0 & SLK0). unfold str_base, struct_size, argc, envc in P0LO.
    destruct (stack_pieces sp0 argv envp uid hw rnd mm IMG) as (_ & ARGVP & _).
    assert (A0NN : ~ In (Z_to_bv 8 0) arg0) by (rewrite EARGV in NONUL; inversion NONUL; assumption).
    assert (A0LEN : Z.of_nat (length arg0) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN; assumption).
    unfold argc. zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.

    zstep. zstep. zstep.
    pose proof (u64ro_read mm (usp0 + 8) (argv_ptrs sp0 argv envp ++ [Z_to_bv 64 0]) 0 (Z_to_bv 64 p0) (Z_to_bv 64 (usp0 + 8))
                  ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP0) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep.

    apply evt_done.
    eapply implM_bind.
    { eapply (FPR (PDUsage (nth 0 (argv_Z argv) []))) with (lo := usp0 - 8388608) (canary := guard_word);
        [apply stderr_wfile0_wfile; exact SE| reflexivity| | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia| unfold GLOBALS_TOP; lia| rewrite unsigned_lit by lia; lia
        | apply (RHEAP_ssp _ _ _ HP)| exact MI| vm_compute; reflexivity].
      cbn [diag_args]. split; [reflexivity|]. exists slack0.
      rewrite EARGV. cbn [argv_Z map nth]. rewrite unsigned_lit by lia.
      unfold zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
      split; [exact STR0|]. split; [apply map_unsigned_pos; exact A0NN|]. split; [lia|].
      split; [lia|]. split; [right; rewrite unsigned_lit by lia; lia|]. split; [unfold GLOBALS_TOP; lia| lia]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x13cd0)) with (Z_to_bv 64 0x13cd0) by (symmetry; rpc).
    pose proof (agree_on_of_munch rsegs _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0x2b480 <= a < 0x2b480 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x2b480, 0x2b480 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (OUT2 : forall a, (0x10000 <= a < 0x5d000 /\ ~ (0x2b480 <= a < 0x2b480 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x2b480, 0x2b480 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    eapply implM_evt; [| intros msx Hx; exact (EXK at_parser 2 _ Q msx Hx)]. unfold MFRAME in FR.
    apply (rw_cells_agree rsegs _ _ _ _ _ AG) in FR; [| intros a Ha; apply OUT; cbn in Ha; lia].
    zstep.
    eapply (main_return sp0 argv TID VSP CEIL HT 2 (ps_init (reservedZ rsegs) alloc_ceiling) []).
    - exact FR.
    - unfold LO. replace (usp0 - 8388608) with (usp0 + -8388608) in ST2 by lia. exact ST2 || exact ST2.
    - eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
    - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. lia.
    - cbn [ps_so ps_init]. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SO].
    - apply stderr_wfile_file. exact SEW.
    - exact MI2.
  Qed.
End A2.
