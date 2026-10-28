(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX ShapeLaws MmapSim AllocSim FileSim AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame MemcpyLib Hoare BBFrame MallocDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_call U_exit_base U_stdio_defs U_exit U_startup U_main_entry U_enframe_base U_read_base.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_main_open_defs.  (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_stdio_oomltac () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "Corelib.Init.Datatypes.None"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_oom"].


Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


Definition is_kzero_cov (b : expr) (k n : Z) (K : kentry) : bool :=
  match K with
  | KZero (SA b' k') (ELit n') => expr_eqb b b' && Z.leb k' k && Z.leb (k + n) (k' + n')
  | _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msg_oom_img : ltac2:(CDefT.buildp (gd_tbl_P_stdio_oomltac ()) "(0.(1.(2.(3.&8.)))(4.$5.L,(3.&40.)(6.(3.&8.))(7.&40.+1040<.)#13.)(8.(2.(3.&8.))$9.))")
(* [comment removed for export] *).
Proof. vm_compute. reflexivity. Qed.

Ltac oom_exit_pre HL P0 MFS :=
  lazymatch goal with
  | HR : regs_ok ?E ?sr ?R, HK : know_ok _ _ ?M ?kn |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | try rewrite MFS; apply exit_leaf_eq; lia ];
    apply ref_exit_Z;
    let Ktid := fresh "Ktid" in let Hst := fresh "Hst" in let Htc := fresh "Htc" in
    pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev] in Ktid;
    lazymatch type of P0 with vals_ev _ 0 = ?sp0 =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x5d0c8), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0x7d790), (Z_to_bv 64 0);
    split; [|split; [first [reflexivity | assumption] | split; [first [reflexivity | assumption] |]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; lia
      | lit_u; lia
      | cbn [ev]; cbn [ev] in Ktid; lia
      | lit_u; change (381128 - 168)%Z with 0x5d020%Z;
        krd HK 0x5d020%Z 4%nat Htc; rewrite Htc; cbn [ev];
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; cbn [ev] in Ktid; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK
      | krd_solve HK                                                       (* [comment removed for export] *)
      | exists false; unfold atexit_st, atexit_none; split; krd_solve HK ]  (* [comment removed for export] *)
    | left; split; [reflexivity|];
      exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
    end
  end.

Ltac oom_stdio_exit HL P0 RES_EQ FD2 MFS :=
  (* [comment removed for export] *)
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
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn res];
      change (Z.of_nat (length msg_oom)) with 19%Z; change (Z.of_nat (@length byte [])) with 0%Z;
      [ cbn [edenot]; lia
      | cbn [edenot]; lia
      | cbn [edenot]; lit_u; reflexivity
      | lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
        rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
        rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
      | cbn [edenot]; lit_u; lia
      | cbn [edenot]; lit_u; lia                                   (* [comment removed for export] *)
      | cbn [edenot]; lit_u; lia                                   (* [comment removed for export] *)
      | reflexivity
      | cbn [edenot]; change (length msg_oom) with 19%nat;
        rewrite (kimg_rdn RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x1040c 19) in exact i)
                   _ _ 0x1040c 19 HK eq_refl) by (cbn; lia);
        apply msg_oom_img
      | apply FD2
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
        run_block_gen FUEL STOPS scr0 NX false;
        oom_exit_pre HL2 Q0 MFS
      ] end end end end
  end.



Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
