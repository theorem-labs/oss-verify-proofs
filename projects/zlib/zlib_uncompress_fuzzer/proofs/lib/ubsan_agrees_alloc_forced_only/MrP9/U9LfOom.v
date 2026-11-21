(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ModelAmb.
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Require LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes Hoare Frame SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame U9LibStdioCall Spec ShapeLaws LibWritev U9ExitBase U9StdioDefs U9Exit U9MainEntry LibTail U9ReadBase U9World .
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require U9PilotOOM.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require SymDriveKN.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP9 Require U9LfReadErr_defs U9LfReadErr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP9 Require Import U9LfBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SimInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ExitSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Nodes OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Frame OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SpecConsts OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec2Sound OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymRun OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDrive OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDriveX OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDriveH4 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibKnowFrame OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.U9LibStdioCall OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeLaws OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibWritev OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.U9ExitBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.U9StdioDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.U9Exit OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.U9MainEntry OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibTail OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.U9ReadBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.U9World OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP9.U9LfReadErr_defs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP9.U9LfReadErr.S0ReadErr_tail OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP9.U9LfReadErr.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition KEPT_OOM : list nat := [2; 3; 4]%nat.
Definition srOOM0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_OOM 6.

Definition ssA0 : sym_state := SS 0x14b60 srOOM0 [] knLF0 39.
Definition rA {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssA0.
Definition srA {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rA knLF0.
Definition ssA0' : sym_state := SS 0x14ba0 srOOM0 [] knLF0 39.
Definition rA' {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssA0'.
Definition resB {RCa1 : RunCtx}  : stdio_res :=
  Eval vm_compute in match stdio_call 39 srA knA with Some r => r
                     | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Lemma resB_eq {RCa1 : RunCtx}  : stdio_call 39 srA knA = Some resB.
Proof. vm_compute. reflexivity. Qed.
Definition srB0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr resB.
Definition knB0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn resB.
Definition ssB0 {RCa1 : RunCtx}  : sym_state := SS 0x1c5b8 srB0 [] knB0 71.
Definition rB {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssB0.
Definition srB {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rB knB0.

Lemma itinerary_oom {RCa1 : RunCtx}  :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x1c84c%Z, [])
  /\ (fst (fst rA')) = (fst (fst rA)) /\ snd (fst rA') = []
  /\ (sc_ret resB, sc_f resB, sc_fd resB) = (0x1c5b8%Z, 0x23f00%Z, 2%Z)
  /\ (s_pc (fst (fst rB)), snd (fst rB)) = (0x1a37c%Z, []).
Proof.
  repeat apply conj; lazymatch goal with |- @eq ?T ?x ?y => vm_cast_no_check (@eq_refl T y) end.
Qed.

Ltac oom_exit_pre HL P0 MFS :=
  lazymatch goal with
  | HR : regs_ok ?E ?sr ?R, HK : know_ok _ _ ?M ?kn |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq (run_segments RSEGS rc_inp rc_sp rc_mb) _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | try rewrite MFS; apply exit_leaf_eq; lia ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in let Hst := fresh "Hst" in let Htc := fresh "Htc" in
    pose proof (know_nth (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev] in Ktid;
    lazymatch type of P0 with vals_ev _ 0 = ?sp0 =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x74240), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0x94908), (Z_to_bv 64 0);
    split; [|split; [first [reflexivity | assumption] | split; [first [reflexivity | assumption] |]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        pose proof (kwr_store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; lia
      | lit_u; lia
      | cbn [ev]; cbn [ev] in Ktid; lia
      | lit_u; change (475712 - 168)%Z with 0x74198%Z;
        krd HK 0x74198%Z 4%nat Htc; rewrite Htc; cbn [ev];
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; cbn [ev] in Ktid; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | exists (Z_to_bv 64 0x23ed8); krd_solve HK
      | left; split; krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK ]
    | left; split; [reflexivity|];
      exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
    end
  end.

Ltac oom_stdio_exit HL P0 RES_EQ FD2 MFS :=
  lazymatch goal with
  | HR : regs_ok ?E _ _, HK : know_ok _ _ _ _ |- _ =>
      let En := eval hnf in E in change E with En in HR; change E with En in HK end;
  lazymatch goal with
  | HR : regs_ok ?E ?sr ?R, HK : know_ok _ _ ?M ?kn |- realizes _ (mkCfg _ ?model) (t_die msg_oom ?fs) =>
    lazymatch type of HL with length ?vals = ?nv =>
    lazymatch type of P0 with vals_ev _ 0 = ?sp0 =>
    lazymatch type of RES_EQ with stdio_call _ _ _ = Some ?res =>
    lazymatch E with Env _ ?ebs =>
      unfold t_die, W;
      apply (stdio_call_sound vals ebs sr kn R M model res [] msg_oom
               (t_exit (exit_code 2) fs) HR HK (eq_trans (f_equal (fun n => stdio_call n sr kn) HL) RES_EQ));
      (* [res] is now an application of a threaded definition; unfold its head constant *)
      (let rec hd t := lazymatch t with ?f _ => hd f | _ => constr:(t) end in
       let h := hd res in cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn h]);
      change (Z.of_nat (length msg_oom)) with 19%Z; change (Z.of_nat (@length byte [])) with 0%Z;
      [ cbn [edenot]; lia
      | cbn [edenot]; lia
      | cbn [edenot]; lit_u; reflexivity
      | lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
        rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
        rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; try lit_u; lia
      | cbn [edenot]; lit_u; try lit_u; lia
      | cbn [edenot]; lit_u; unfold TASK_SIZE; lia
      | cbn [edenot]; lit_u; try lit_u; unfold TASK_SIZE; lia
      | reflexivity
      | cbn [edenot]; change (length msg_oom) with 19%nat;
        rewrite (kimg_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10320 19) in exact i)
                   _ _ 0x10320 19 HK eq_refl) by (cbn; lia);
        apply U9PilotOOM.msg_oom_img
      | apply FD2
      | (* LibWritev's channel-reader premise (the section's Hrdr) *)
        first [reflexivity | assumption]
      | first [reflexivity | assumption]
      | first [reflexivity | assumption]
      | apply t_exit_has_nil
      | clear HR HK; try clear R M;
        let R2 := fresh "R" in let M2 := fresh "M" in
        intros R2 M2 HR HK;
        let srX := eval vm_compute in (sc_sr res) in change (sc_sr res) with srX in HR;
        let knX := eval vm_compute in (sc_kn res) in change (sc_kn res) with knX in HK;
        let ret := eval vm_compute in (sc_ret res) in change (sc_ret res) with ret;
        let vals2 := fresh "vals" in let HL2 := fresh "HL" in let Q0 := fresh "P0" in
        set (vals2 := vals ++ junk_vals R2) in *;
        assert (HL2 : length vals2 = (nv + 32)%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity);
        cbn [Nat.add] in HL2;
        assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
        clearbody vals2; clear HL P0;
        let NX := eval vm_compute in (nv + 32)%nat in
        OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDriveKN.run_block_gen_kn FUEL STOPS scr0 NX false;
        oom_exit_pre HL2 Q0 MFS
      ] end end end end
  end.


Section OomTail.
Context {RCa1 : RunCtx}.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  (* the launch's channel reader (LibWritev's premise), form (B). *)
  Hypothesis Hrdr : m_channel_reader model = true.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Lemma oom_sym : forall (pc : Z) vals R M,
    (pc = 0x14b60 \/ pc = 0x14ba0)%Z ->
    length vals = 39%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV BL vals) srOOM0 R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV BL vals) M knLF0 ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
               (t_die msg_oom (m_fs model)).
  Proof.
    intros pc vals R M Hpc HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    assert (STEP : forall T,
      (forall R' M', regs_ok (ENV BL vals) srA R' -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (ENV BL vals) M' knA ->
         realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R' (Z_to_bv 64 0x1c84c) M' (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model) T) ->
      realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model) T).
    { intros T HT. destruct Hpc as [-> | ->].
      - run_blk scr0 39%nat. apply HT; assumption.
      - run_blk scr0 39%nat. apply HT; assumption. }
    apply STEP. clear STEP HR HK R M. intros R M HR HK.
    oom_stdio_exit HL P0 resB_eq Hfd2 (@eq_refl _ (m_fs model)).
  Qed.


  Variables (tid : Z) (R : bvmap 5 word) (M : word -> option byte).
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x74240.
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) lf_ivs.
  Hypothesis Mtid : cell M 0x74198 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Variable cw : Z.
  Hypothesis Mgot : cell M 0x22ec0 8 0x944a8.
  Hypothesis Mcanary : cell M 0x944a8 8 cw.
  Hypothesis Mnl : cell M 0x944cb 1 0.

  Definition valsOOM : list word := valsRE sp0 sp0 tid R cw.
  Let E : env := ENV BL valsOOM.

  Lemma valsOOM_len : length valsOOM = 39%nat.
  Proof. apply valsRE_len. Qed.

  Lemma evOOM_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof. intros i Hi. apply (evRE_junk sp0 BL sp0 tid R cw i Hi). Qed.

  Ltac reg_caseOOM :=
    cbn [nth srOOM0 all_regs];
    first [ lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evOOM_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  Lemma regs_okOOM : regs_ok E srOOM0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseOOM.
  Qed.

  Lemma know_okOOM : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M knLF0.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply (know_okLF sp0 BL Hvsp sp0 tid R M cw Mstack Mimg Mtid Htid Mgot Mcanary Mnl); lia.
  Qed.

  Theorem ref_oom_tail : forall pc : Z, (pc = 0x14b60 \/ pc = 0x14ba0)%Z ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
               (t_die msg_oom (m_fs model)).
  Proof.
    intros pc Hpc.
    eapply (oom_sym pc valsOOM R M Hpc valsOOM_len eq_refl regs_okOOM know_okOOM).
  Qed.
End OomTail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

