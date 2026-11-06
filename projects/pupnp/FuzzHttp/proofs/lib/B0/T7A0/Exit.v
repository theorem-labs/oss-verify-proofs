(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts Globals IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Stdio_iface.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Ltac amo_decide :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let b := eval vm_compute in (amo_aligned wd a) in
      replace (amo_aligned wd a) with b by (vm_compute; reflexivity); cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      let b := eval vm_compute in (Z.eqb (bv_unsigned x) (bv_unsigned y)) in
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with b by (vm_compute; reflexivity); cbv iota
  end.

Ltac amo_step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

Ltac astep := lstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).
Ltac rel_frame_at sp lo a b :=
  lazymatch goal with FRx : rw_cells asegs _ (bv_unsigned sp + a)%Z _, STx : stk asegs _ lo _ |- _ => release_frame FRx STx (bv_unsigned sp + b)%Z end.
Ltac clear_stk_lo lo := repeat match goal with STo : stk asegs _ lo _ |- _ => clear STo end.

Notation RTPA := 0x5e75b0%Z (only parsing).

Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.

Definition dtor_WL : list ivl := Eval vm_compute in dtor_W.
Lemma dtor_WL_eq : dtor_WL = dtor_W.
Proof. vm_compute. reflexivity. Qed.

Definition exit_atx (f0 : byte) (p3 p4 : list byte) (m : word -> option byte) : Prop :=
  (rw_cells asegs m 0x607600 [C1 f0; CB 3 p3; C4 z64; C4 (Z_to_bv 64 1); CB 4 p4; C8 (Z_to_bv 64 0x607618); C8 z64; C8 (Z_to_bv 64 0x95694); C8 z64]
   /\ rw_cells asegs m 0x607720 [C8 (Z_to_bv 64 0x75abc); C8 z64])
  \/ (rw_cells asegs m 0x607600 [C1 f0; CB 3 p3; C4 z64; C4 (Z_to_bv 64 2); CB 4 p4; C8 (Z_to_bv 64 0x607618); C8 z64; C8 (Z_to_bv 64 0x95694); C8 (Z_to_bv 64 0x95694)]
      /\ rw_cells asegs m 0x607720 [C8 (Z_to_bv 64 0x75abc); C8 (Z_to_bv 64 0x86484)]
      /\ rw_cells asegs m 0x5e6b94 [C1 (Z_to_bv 8 0)]).

Section ExitPrefix.
  Context {HC : HasCeiling}.
  Hypothesis DT : asan_dtor_stmt.

  Definition exit_W (lo hi : Z) : list ivl := [(lo, hi); (0x607820, 0x607824); (0x607600, 0x607618); (0xb0ed0, 0xb0ed1)]%Z.
  #[using="Type"] Lemma asan_env_exit_frame : forall m m' lo hi, asan_env asegs m -> munch (exit_W lo hi) m m' -> wmono asegs m m' ->
    (alloc_ceiling <= lo)%Z -> asan_env asegs m'.
  Proof.
    intros m m' lo hi AE MU WM CLO. pose proof (@alloc_ceiling_bounds HC) as CEILB.
    eapply asan_env_frame; [exact AE | exact MU | exact WM |]. unfold exit_W. env_safe_tac.
  Qed.

  Definition rexit_prefix_post (sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo code : Z) (s0 ra : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR (Z_to_bv 64 0x95754) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTPA) t0 t1 t2 (Z_to_bv 64 code) s1
                   a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x9ba44) fc None m' (seg_rom asegs)
      /\ munch (exit_W lo (bv_unsigned sp) ++ dtor_WL)%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp + -16)
      /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
      /\ asan_env asegs m'.

  #[using="DT"] Lemma rexit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (f0 : byte) (p3 p4 : list byte) (dso : word) (cf : byte)
      (cdt thr sec : byte) (tm1 : word),
    stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0x5e7508 [C4 (Z_to_bv 64 t)] ->
    rw_cells asegs m 0x607820 [C4 z64] ->
    exit_atx f0 p3 p4 m ->

    rw_cells asegs m 0x1463e0 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x607840 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells asegs m 0xab9f8 [C8 (Z_to_bv 64 0xaa750); C8 (Z_to_bv 64 0xaa740)] ->
    rw_cells asegs m 0xaa740 [C8 (Z_to_bv 64 0x8ba48); C8 (Z_to_bv 64 0x324b8)] ->
    rw_cells asegs m 0xb0ed0 [C1 cf] ->
    rw_cells asegs m 0xaad00 [C8 (Z_to_bv 64 0x955cc); C8 z64] ->
    rw_cells asegs m 0xaca40 [C8 dso] ->
    asan_env asegs m -> globals_shadow m ->
    mem_inv asegs m ->
    tp = Z_to_bv 64 RTPA -> a0 = Z_to_bv 64 code ->
    (0 < t < 2^31)%Z -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 48 - A0_RT_STACK)%Z -> (bv_unsigned sp <= 2^47)%Z ->
    evt asegs (rexit_prefix_post sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code s0 ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x956e8) fc None m (seg_rom asegs)).
  Proof.
    intros until tm1. intros ST TID EXL ATXS COV LCH GF FA CF GCX DSO ENV GSH MI -> -> Ht CLO LO SP47.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (@alloc_ceiling_bounds HC) as CEILB. unfold A0_RT_STACK in LO.
    pose proof (munch_refl (exit_W lo (bv_unsigned sp) ++ dtor_WL)%Z m) as MU.
    pose proof (munch_refl (exit_W lo (bv_unsigned sp)) m) as MU0. unfold exit_W, dtor_WL in MU, MU0. cbn [app] in MU.
    pose proof (wmono_refl asegs m) as WM.
    destruct ATXS as [(ATX & ATA) | (ATX & ATA & ICB)].
    all: carve_frame 16%nat ST.
    all: do 6 lstep.
    all: replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    all: lstep. all: lstep.

    all: amo_step. all: replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    all: lstep. all: if_false. all: amo_step. all: lstep. all: if_false.
    all: lstep. all: change (bv_swrap 32 (0 + 0)) with 0%Z.
    all: lstep. all: if_cases K; zify_cond K; [exfalso; lia|]. all: clear K. all: lstep. all: if_true.
    all: lstep. all: lstep.

    all: carve_frame 48%nat ST. all: steps_to 0xa3a70%Z.

    all: steps_to 0x95530%Z.

    all: steps_to 0x9553c%Z.
    1: replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    2: replace (sx32 (Z_to_bv 64 2)) with (Z_to_bv 64 2) by (vm_compute; reflexivity).
    all: steps_to 0x95558%Z.
    all: steps_to 0xa3cf8%Z.

    all: steps_to 0x95584%Z.

    all: steps_to 0x95590%Z.
    2: at_pc 0x95590%Z.
    2: replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    2: steps_to 0xa3cf8%Z. 2: at_pc 0xa3cf8%Z.
    2: steps_to 0x95584%Z. 2: at_pc 0x95584%Z.
    2: steps_to 0x95590%Z. 2: at_pc 0x95590%Z.
    all: replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    all: steps_to 0xa3cf8%Z.

    all: steps_to 0x9574c%Z.
    all: release_frame FR0 ST (bv_unsigned sp + -16)%Z.

    all: lstep. all: carve_frame 32%nat ST. all: steps_to 0x324b8%Z.

    all: carve_frame 16%nat ST.
    all: do 8 lstep.
    all: lstep. all: if_cases K.
    1, 3: steps_to 0x955cc%Z. 1, 3: lstep.
    all: steps_to 0x32538%Z. all: steps_to 0x956cc%Z.
    all: rel_frame_at sp lo (-64)%Z (-48)%Z.
    all: astep. all: astep. all: astep. all: astep. all: astep.

    all: eapply evt_cut;
      [ eapply (DT _ (bv_unsigned sp + -48)%Z) with (lo := lo); rewrite ?unsigned_lit by lia;
        first [ eapply asan_env_exit_frame; [exact ENV | exact MU0 | exact WM | exact CLO]
              | refine (proj1 (globals_shadow_frame _ _ _ GSH MU0 WM _)); unfold app_ivs; repeat (apply Forall_cons; [first [apply app_iv_stack; lia | apply app_iv_low; lia] |]); apply Forall_nil
              | refine (proj2 (globals_shadow_frame _ _ _ GSH MU0 WM _)); unfold app_ivs; repeat (apply Forall_cons; [first [apply app_iv_stack; lia | apply app_iv_low; lia] |]); apply Forall_nil
              | assumption | unfold A0_RT_STACK; lia | lia ]
      | idtac ].
    all: clear MU0. all: intros ms2 PO. all: destruct_exs PO. all: destruct PO as [E [MUc [WMc PO]]]. all: destruct PO as [MI3 PO]. all: subst ms2.

    all: rewrite <- dtor_WL_eq in MUc. all: unfold dtor_WL in MUc. all: cbn [app] in MUc.

    all: clear_stk_lo lo.
    all: lazymatch type of MUc with munch _ ?ma ?mx => transport_after_call asegs ma mx MUc WMc; clear MUc WMc; try clear MI; rename mx into m3 end.
    all: destruct_ands PO.
    all: replace (ret_pc (Z_to_bv 64 612044)) with (Z_to_bv 64 612044) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

    all: astep. all: astep.
    all: steps_to 0x95698%Z. all: astep.
    all: lstep.
    all: rel_frame_at sp lo (-48)%Z (-16)%Z.
    all: apply evt_done. all: unfold rexit_prefix_post. all: repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|].
    all: split; [unfold exit_W, dtor_WL; cbn [app]; exact MU|]. all: split; [exact WM|]. all: split; [assumption|].
    all: split; [assumption|]. all: split; [assumption| assumption].
  Time Qed.
End ExitPrefix.

Section ExitProof.
  Context {HC : HasCeiling} {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis DT : asan_dtor_stmt.

  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

  #[using="DT stdio_exit_spec"] Lemma exit_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (f0 : byte) (p3 p4 : list byte) (dso : word) (cf : byte)
      (guard : word) (cdt thr sec : byte) (tm1 : word),
    stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0x5e7508 [C4 (Z_to_bv 64 t)] ->
    rw_cells asegs m 0x607820 [C4 z64] ->
    exit_atx f0 p3 p4 m ->
    rw_cells asegs m 0x1463e0 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x607840 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells asegs m 0xab9f8 [C8 (Z_to_bv 64 0xaa750); C8 (Z_to_bv 64 0xaa740)] ->
    rw_cells asegs m 0xaa740 [C8 (Z_to_bv 64 0x8ba48); C8 (Z_to_bv 64 0x324b8)] ->
    rw_cells asegs m 0xb0ed0 [C1 cf] ->
    rw_cells asegs m 0xaad00 [C8 (Z_to_bv 64 0x955cc); C8 z64] ->
    rw_cells asegs m 0xaca40 [C8 dso] ->
    asan_env asegs m -> globals_shadow m ->
    rw_cells asegs m 0x607ca8 [C8 z64] ->
    rw_cells asegs m 0xaf9f0 [C8 (Z_to_bv 64 0xaf908)] -> stdin_file m ->
    rw_cells asegs m 0xaf900 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells asegs m 0xaf810 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells asegs m 0xab9c8 [C8 (Z_to_bv 64 0x6075f0)] -> rw_cells asegs m 0x6075f0 [C8 guard] ->
    mem_inv asegs m ->
    tp = Z_to_bv 64 RTPA -> a0 = Z_to_bv 64 code ->
    (0 < t < 2^31)%Z -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 48 - A0_RT_STACK)%Z -> (bv_unsigned sp <= 2^47)%Z ->
    implM asegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x956e8) fc None m (seg_rom asegs)).
  Proof.
    intros until tm1. intros ST TID EXL ATXS COV LCH GF FA CF GCX DSO ENV GSH OFL SIU SIF SOU SEU SOF SEF GG GU MI -> -> Ht CLO LO SP47.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (@alloc_ceiling_bounds HC) as CEILB. pose proof LO as LO'. unfold A0_RT_STACK in LO'.

    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1. unfold stdin_file, stdin_cells in SIF.
    unfold Driver.exit_model.
    eapply (implM_bind asegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 fc' m',
                 ms' = MS (mkR (Z_to_bv 64 0x95754) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x95754) fc' None m' (seg_rom asegs))).
    -
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
      eapply evt_cut.
      { eapply rexit_prefix_spec; first [exact DT | exact ST | exact TID | exact EXL | exact ATXS | exact COV | exact LCH | exact GF | exact FA | exact CF | exact GCX
                                        | exact DSO | exact ENV | exact GSH | exact MI | reflexivity | lia]. }
      intros ms1 PO. unfold rexit_prefix_post in PO. destruct_exs PO. destruct PO as [E [MUc [WMc PO]]]. destruct PO as [MI1 PO]. subst ms1.
      unfold exit_W, dtor_WL in MUc. cbn [app] in MUc.
      repeat match goal with STo : stk asegs _ lo _ |- _ => clear STo end.
      lazymatch type of MUc with munch _ ?ma ?mx => transport_after_call asegs ma mx MUc WMc; clear MUc WMc; rename mx into m1 end.
      destruct PO as (ST1 & FR1 & ENV1).
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0x95754)) with (Z_to_bv 64 0x95754) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; unfold file_cells; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; unfold file_cells; exact SEF1
           | |- stdin_file _ => unfold stdin_file, stdin_cells; exact SIF
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    -
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Time Qed.
End ExitProof.
