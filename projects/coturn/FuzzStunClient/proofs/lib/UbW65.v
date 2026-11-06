(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes MmapSim AllocSim FileSim AgentLib SpecConsts SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame UbLibStdioCall Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LibWritev RefNodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbExitBase UbStdioDefs UbExit.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbStartup UbMainEntry.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import MallocDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbEnframeBase UbEnframe UbReadBase.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbPilotOOM_defs UbPilotOOM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymXfer SymAbove UbW65_defs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import ShapeLawsX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefNodesX.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require AsanCeil.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymAboveX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymDriveLet SymDriveLetUb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveX.run_block_with ::= run_block_with_let_img.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require UbW65_lits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_sr ::= constr:(UbW65_lits.LITS_SR).
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_lg ::= constr:(UbW65_lits.LITS_LG).
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SymDriveLet.l9_lits_kn ::= constr:(UbW65_lits.LITS_KN).
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_nobignat.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.
Tactic Notation "run_blockW" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX false.
Tactic Notation "run_blockW_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_W scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bt_ne_not : forall (x : word), (bv_unsigned x < 2 ^ 64 - 1)%Z ->
  branch_taken BC_NE (alu64 ALU_XOR x (Z_to_bv 64 (-1))) (Z_to_bv 64 0) = true.
Proof.
  intros x Hx. cbn [branch_taken]. apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
  change (alu64 ALU_XOR x (Z_to_bv 64 (-1))) with (bv_xor x (Z_to_bv 64 (-1))).
  pose proof (u64_range x).
  rewrite bv_xor_unsigned. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  change ((-1) mod 2 ^ 64)%Z with (2 ^ 64 - 1)%Z. change (0 mod 2 ^ 64)%Z with 0%Z.
  intros E. apply Z.lxor_eq in E. lia.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_set_have : forall E sr R (rd : reg) v e,
  regs_ok E sr R -> getr R rd = v -> edenot E e = v -> rd <> 0%bv ->
  regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
  intros E sr R rd v e HR Hv He Hrd r.
  pose proof (regs_ok_set E sr R rd v e HR Hrd He r) as H.
  rewrite <- H. destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hrd. exact Hv.
  - rewrite getr_other by exact Hne. reflexivity.
Qed.

Lemma callee_saved_no0 : ~ In (0%bv : reg) callee_saved.
Proof.
  unfold callee_saved. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

Definition is_kzero_cov (b : expr) (k n : Z) (K : kentry) : bool :=
  match K with
  | KZero (SA b' k') (ELit n') => expr_eqb b b' && Z.leb k' k && Z.leb (k + n) (k' + n')
  | _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x36c60), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0x57320), (Z_to_bv 64 0);
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
      | lit_u; change (224352 - 168)%Z with 0x36bb8%Z;
        krd HK 0x36bb8%Z 4%nat Htc; rewrite Htc; cbn [ev];
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
      | repeat split; krd_solve HK ]
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
      | (* [comment removed for export] *) cbn [edenot]; lit_u; lia
      | cbn [edenot]; lia
      | cbn [edenot]; lit_u; reflexivity
      | pose proof rw_bytes_max_ge17; lia
      | lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
        rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite P0;
        rewrite (u_small (bv_unsigned _ + _)) by lia; lit_u; lia
      | cbn [edenot]; lit_u; lia
      | reflexivity
      | cbn [edenot]; change (length msg_oom) with 19%nat;
        rewrite (kimg_rdn RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x10317 19) in exact i)
                   _ _ 0x10317 19 HK eq_refl) by (cbn; lia);
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

Section World.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* [comment removed for export] *)
  Variable fd3 : FdEntry.
  (* [comment removed for export] *)
  Variable SI : (word -> option byte) -> Prop.
  Hypothesis SI_step : forall M M' : word -> option byte,
    (forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M' a = M a) -> SI M -> SI M'.

  #[local] Notation ENVv := (ENV a0s path).
  (* [comment removed for export] *)
  #[local] Notation RES := (segments_reserved RSEGS).

  (* [comment removed for export] *)
  Ltac si_block HSI Rn Mn :=
    lazymatch goal with
    | EQM : ?M' = mem_denot ?E ?Mo ?log, HK : know_ok ?segs ?E ?M' ?kn, HR : regs_ok ?E _ ?R' |- _ =>
        let H := fresh "HSI" in
        assert (H : SI M');
        [ apply (SI_step Mo M'); [| exact HSI]; intros xa Hxa; rewrite EQM;
          apply (mem_denot_above_kbx segs E M' Mo kn log 0%nat 0x58000 0x7fff7f800000 xa HK);
          [ vm_compute; reflexivity | lia | cbn [ev ENV]; pins; lia | cbn [ev ENV]; pins; lia | lia | lia ]
        | clear HSI EQM; try clear Mn; rename H into HSI; try rename M' into Mn; try clear Rn; try rename R' into Rn ]
    end.

  (* [comment removed for export] *)
  Ltac si_fill HSI :=
    lazymatch goal with
    | |- SI (zfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply zfill_out; rewrite ?u64_lit by lia; lia
    | |- SI (unfill ?a ?n ?M) => apply (SI_step M); [| exact HSI]; intros xa Hxa; apply unfill_outside; rewrite ?u64_lit by lia; lia
    end.

  (* [comment removed for export] *)
  Definition fdsV : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition modelV (VM : VmMaps) : Model := mkModelC fdsV VM stdin0 fs0 None (Some tid) None.

  Lemma fdsV_2 : fd_lookup fdsV (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof using Type. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma mV_vmmaps : forall VM, m_vmmaps (modelV VM) = VM.  Proof using Type. reflexivity. Qed.
  Lemma mV_fs : forall VM, m_fs (modelV VM) = fs0.  Proof using Type. reflexivity. Qed.
  Lemma mV_fds : forall VM, m_fds (modelV VM) = fdsV.  Proof using Type. reflexivity. Qed.
  Lemma mV_fd2 : forall VM, fd_lookup (m_fds (modelV VM)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof using Type. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition model1V : Model := mkModelC fdsV (mkVmMapsFull RES [] [] brk brk LIM mbase sp0) stdin0 fs0 None (Some tid) None.

  Definition brk_ok_entry (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srD2 R -> know_ok RSEGS (ENVv vals) M knD2 -> SI M ->
      realizes RSEGS
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x1ca9c)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom RSEGS))
               (mkModelC fdsV (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk
                                            (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                        stdin0 fs0 None (Some tid) None)) KB.

  Definition mmap_ok_entry (KB : TSet) : Prop :=
    forall vals R M (hint a : word),
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srE R -> know_ok RSEGS (ENVv vals) M knE -> SI M ->
      grant_ok_na_pin model1V a 8192 = true ->   (* [comment removed for export] *)
      realizes RSEGS (mkCfg (mkst (regupd R 10 a) (Z_to_bv 64 0x1dbac)
                                    (unfill a (Z_to_bv 64 8192) M) (seg_rom RSEGS))
                              (noaccess_model a (Z_to_bv 64 8192) model1V)) KB.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma w65_oomN : forall vals R M VM,
    length vals = 72%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENVv vals) srN0 R -> know_ok RSEGS (ENVv vals) M knW2 ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1dbac) M (seg_rom RSEGS)) (modelV VM)) (t_die msg_oom fs0).
  Proof using Hvsp Hplen.
    intros vals R M VM HL P0 HR HK.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    run_block scr0 72%nat.
    oom_stdio_exit HL P0 resX_eq (mV_fd2 VM) (mV_fs VM).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable K : TSet.

  (* [comment removed for export] *)
(* [comment removed for export] *)
  Definition w65_vm (VM : VmMaps) (mb gm : word) : Prop :=
    vm_reserved VM = RES /\ vm_limit VM = LIM /\
    ((vm_maps VM = [(gm, Z_to_bv 64 69632); (mb, Z_to_bv 64 8192)]
      /\ (bv_unsigned gm + 69632 <= bv_unsigned mb \/ bv_unsigned mb + 8192 <= bv_unsigned gm)%Z)
     \/ (vm_maps VM = [(gm, Z_to_bv 64 69632); (Z_to_bv 64 (bv_unsigned mb + 4096), Z_to_bv 64 4096)]
      /\ (bv_unsigned gm + 69632 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned gm)%Z)).

  Definition exitG_branch : Prop :=
    forall vals R M VM,
      length vals = 105%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
      regs_ok (ENVv vals) srZ R -> know_ok RSEGS (ENVv vals) M knZ ->
      vm_pre VM sp0 brk (vals_ev vals 72) -> w65_vm VM brk (vals_ev vals 72) -> SI M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13b14) M (seg_rom RSEGS)) (modelV VM)) K.

  Lemma w65_G : forall vals R M VM,
    exitG_branch ->
    length vals = 73%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
    regs_ok (ENVv vals) srG0 R -> know_ok RSEGS (ENVv vals) M knG0 ->
    vm_pre VM sp0 brk (vals_ev vals 72) -> w65_vm VM brk (vals_ev vals 72) -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1dbac) M (seg_rom RSEGS)) (modelV VM)) K.
  Proof using Hvsp Hbrk Hplen SI_step.
    intros vals R M VM EXIT HL P0 P2 P70 P5 HR HK HVM HVS HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_krange gx) in exact i) _ HK eq_refl)
      as Kgm; cbn [kentry_ok edenot ev ENV] in Kgm.
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_kalign gx) in exact i) _ HK eq_refl)
      as Kga; cbn [kentry_ok edenot ev ENV] in Kga.
    pose proof (know_nth RSEGS _ _ knG0 ltac:(let i := kidx knG0 (is_kdisj bx gx) in exact i) _ HK eq_refl)
      as Kgd; cbn [kentry_ok] in Kgd; unfold estart in Kgd; cbn [a_base a_off edenot ev ENV] in Kgd; rewrite P70 in Kgd.
    set (gm := vals_ev vals 72) in *.
    (* [comment removed for export] *)
    run_block_keep scrG 73%nat.
    { unfold sc_denot. cbn [edenot ev ENV]. apply bt_ne_not. subst gm. lia. }
    si_block HSI R M.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      krdv HK 70%nat 4136%Z 8%nat Hmem; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P70; lia|];
      krdv HK 70%nat 4152%Z 8%nat Hmw; [apply flat_intro; cbn [edenot ev ENV]; rewrite ?P70; lia|];
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kzero_cov gx 9 8) in exact i) _ HK eq_refl) as Kz;
      cbn [kentry_ok] in Kz; unfold elenZ, estart in Kz; cbn [a_base a_off edenot ev ENV] in Kz;
      pose proof (kwr_store_ok RSEGS E _ kn ltac:(let i := kidx kn (is_kwr_cov gx 13 69615) in exact i)
                    _ _ _ 13 (Z.to_nat 69615) HK eq_refl ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as Hok;
      pose proof (know_nth RSEGS _ _ kn ltac:(let i := kidx kn (is_kimg_cov 69824 96) in exact i) _ HK eq_refl) as Kimg;
      cbn [kentry_ok] in Kimg
    end.
    fold gm in Kz, Hmem, Hmw, Hok.
    unfold adenot, v_addi in Hmem, Hmw, Hok. cbn [a_base a_off edenot ev ENV] in Hmem, Hmw, Hok.
    rewrite P70 in Hmem, Hmw. fold gm in Hok.
    change (bv_unsigned (Z_to_bv 64 69623)) with 69623%Z in Kz.
    assert (EF : efH M (Z_to_bv 64 1) (bv_unsigned brk + 4120) (bv_unsigned gm) 72480 0 65536 0 0 69616
                     (bv_unsigned gm + 16) 1).
    { constructor.
      - vm_compute. reflexivity.
      - unfold slot_start, UNIT. lia.
      - vm_compute. reflexivity.
      - pose proof (u64_range brk). lia.
      - pose proof (u64_range gm). lia.
      - lia.
      - lia.
      - lia.
      - intros _. vm_compute. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - replace (bv_unsigned brk + 4120 + 16)%Z with (bv_unsigned brk + 4136)%Z by lia.
        rewrite Hmem. subst gm. rewrite Z_to_bv_bv_unsigned. reflexivity.
      - replace (bv_unsigned brk + 4120 + 32)%Z with (bv_unsigned brk + 4152)%Z by lia. exact Hmw.
      - replace (bv_unsigned gm + 16 - 4)%Z with (bv_unsigned gm + 9 + 3)%Z by lia. apply (proj2 Kz). lia.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 9 + 4)%Z by lia. apply (proj2 Kz). lia.
      - intros C. exfalso. apply C. reflexivity.
      - replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (Z.to_nat (69616 - 1)) with (Z.to_nat 69615) by reflexivity. exact Hok.
      - intros j Hj. unfold SCT. apply (proj2 (proj2 Kimg)). lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x13b14)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x13b14) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 (bv_unsigned brk + 4120)).
    { regv HR (10:reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
      rewrite P70. reflexivity. }
    assert (G11 : getr R 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity).
    assert (G12 : getr R 12 = Z_to_bv 64 65536) by (regv HR (12:reg); reflexivity).
    assert (G13 : getr R 13 = Z_to_bv 64 1) by (regv HR (13:reg); reflexivity).
    destruct (enframe_run M (Z_to_bv 64 1) _ _ _ _ _ _ _ _ _ _ EF R (seg_rom RSEGS) (Z_to_bv 64 0x13b14)
                G1 RT G10 G11 G12 G13) as (R2 & Hms & Hkeep & HA0).
    clear RT G1 G10 G11 G12 G13.
    replace (Z_to_bv 64 120860) with (0x1d81c : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    replace (memF M 0 65536 69616 (bv_unsigned gm + 16) 1) with (mem_denot (ENVv vals) M LOGE).
    2:{ unfold memF. cbv delta [mF mE mE1 mD] beta zeta.
        replace (69616 - 4 - 65536 - 16 * 1)%Z with 4060%Z by reflexivity.
        replace (69616 * 0 / 16 + 1)%Z with 1%Z by reflexivity.
        change (1 =? 0)%Z with false. change (4060 =? 0)%Z with false. change (4060 <? 5)%Z with false.
        cbv iota.
        replace (0 + 32 * res_code 4060)%Z with 160%Z by reflexivity.
        replace (bv_unsigned gm + 16 - 3)%Z with (bv_unsigned gm + 13)%Z by lia.
        replace (bv_unsigned gm + 16 - 2)%Z with (bv_unsigned gm + 14)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 4)%Z with (bv_unsigned gm + 28)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 3)%Z with (bv_unsigned gm + 29)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 - 2)%Z with (bv_unsigned gm + 30)%Z by lia.
        replace (bv_unsigned gm + 16 + 16 * 1 + 65536)%Z with (bv_unsigned gm + 65568)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 5)%Z with (bv_unsigned gm + 69623)%Z by lia.
        replace (bv_unsigned gm + 16 + 69616 - 4 - 4)%Z with (bv_unsigned gm + 69624)%Z by lia.
        unfold LOGE. cbn [mem_denot]. unfold adenot. cbn [a_base a_off edenot gx ev ENV]. fold gm. unfold v_addi.
        change (word_to_le_bytes 1 (Z_to_bv 64 160)) with [Z_to_bv 8 160].
        change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
        change (word_to_le_bytes 1 (Z_to_bv 64 224)) with [Z_to_bv 8 224].
        reflexivity. }
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?MG ?kn =>
      pose proof (carry_after RSEGS E MG LOGE kn [] knZ [] _ ltac:(vm_compute; reflexivity)
                    ltac:(cbn [log_flat LOGE]; unfold flat, estart; cbn [a_base a_off edenot gx ev ENV]; fold gm;
                          repeat split; lia)
                    HK ltac:(constructor)) as HK2
    end.
    (* [comment removed for export] *)
    assert (HSI2 : SI (mem_denot (ENVv vals) M LOGE)).
    { apply (SI_step M); [|exact HSI]. intros xa Hxa.
      apply (mem_denot_above_kbx RSEGS (ENVv vals) _ M knZ LOGE 0%nat 0x58000 0x7fff7f800000 xa HK2);
        [vm_compute; reflexivity | lia | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia | lia]. }
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr R R2 callee_saved ltac:(rewrite HL; vm_compute; reflexivity)
                    HR Hkeep callee_saved_no0) as HR2 end.
    rewrite HL in HR2. clear HR.
    set (vals2 := vals ++ junk_vals R2) in *.
    assert (HL2 : length vals2 = 105%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
    assert (Q72 : vals_ev vals2 72 = gm) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); reflexivity).
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2.
    pose proof (regs_ok_set_have (ENVv vals2) _ R2 10 _ (EAlu ALU_ADD gx (ELit 32)) HR2 HA0
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot gx ev ENV];
                        rewrite Q72; f_equal; lia) ltac:(discriminate)) as HR3.
    clear HR2.
    lazymatch type of HR3 with regs_ok _ ?sr _ => replace sr with srZ in HR3 by (vm_compute; reflexivity) end.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK3 end.
    clear HK2 HK.
    change (Env (vals_ev (vals ++ junk_vals R2)) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HK3.
    change (mem_denot (Env (vals_ev vals) (blobs_ev (blobs0 a0s path))) M LOGE) with (mem_denot (ENVv vals) M LOGE) in HSI2.
    apply (EXIT vals2 R2 _ VM HL2 Q0 Q2 Q70 Q5 HR3 HK3); [rewrite Q72; exact HVM | rewrite Q72; exact HVS | exact HSI2].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition VMk : VmMaps :=
    mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition VMo : VmMaps :=
    mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [(brk, Z_to_bv 64 4096)] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition VMd : VmMaps :=
    mkVmMapsFull RES [(Z_to_bv 64 (bv_unsigned brk + 4096), Z_to_bv 64 4096)] [] brk
                 (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0.
  Definition vm_mid (VM : VmMaps) : Prop := VM = VMk \/ VM = VMo \/ VM = VMd.

  Lemma RES_eq : RES = [(Z_to_bv 64 65536, Z_to_bv 64 12288); (Z_to_bv 64 77824, Z_to_bv 64 73728);
                        (Z_to_bv 64 151552, Z_to_bv 64 4096); (Z_to_bv 64 155648, Z_to_bv 64 204800)].
  Proof using Type. vm_compute. reflexivity. Qed.

  Lemma vm_mid_shape : forall VM, vm_mid VM ->
    vm_reserved VM = RES /\ vm_limit VM = LIM
    /\ exists mp ms, vm_maps VM = [(mp, ms)]
       /\ (bv_unsigned ms = 8192 /\ mp = brk \/ bv_unsigned ms = 4096 /\ bv_unsigned mp = bv_unsigned brk + 4096)%Z.
  Proof using path Hbrk Hplen.
    intros VM HV. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct HV as [-> | [-> | ->]]; cbn [VMk VMo VMd vm_reserved vm_limit vm_maps];
      (split; [reflexivity|]); (split; [reflexivity|]); eexists _, _; (split; [reflexivity|]);
      rewrite ?u64_lit by lia.
    - left. split; [reflexivity | reflexivity].
    - left. split; [reflexivity | reflexivity].
    - right. split; reflexivity.
  Qed.

  Lemma vm_mid_grant_exists : forall hint VM, vm_mid VM -> exists a, grant_ok hint (modelV VM) a (page_round_up_Z 69632) = true.
  Proof using path Hvsp Hbrk Hplen.
    intros hint VM HV. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
    change (page_round_up_Z 69632) with 69632%Z.
    apply grant_exists.
    - rewrite mV_vmmaps. destruct HV as [-> | [-> | ->]]; unfold AsanCeil.init_sp_ok; cbn [vm_init_sp]; exact (proj1 Hvsp).
    - lia.
    - rewrite mV_vmmaps, Hr, Hm, RES_eq. repeat constructor; cbn [snd]; rewrite ?u64_lit by lia; lia.
    - rewrite mV_vmmaps, Hr, Hm, RES_eq. cbn [length app Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - apply grant_budget_intro; [reflexivity | reflexivity |]. rewrite mV_vmmaps.
      unfold vm_live_bytes. rewrite Hm, Hl. cbn [live_bytes]. pose proof LIM_ge. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vm_mid_grant : forall hint VM a, vm_mid VM -> grant_ok hint (modelV VM) a 69632 = true ->
    (bv_unsigned a mod 4096 = 0 /\ 0x58000 <= bv_unsigned a /\ bv_unsigned a + 69632 <= bv_unsigned sp0 - 8388608
     /\ (bv_unsigned brk + 8192 <= bv_unsigned a \/ bv_unsigned a + 69632 <= bv_unsigned brk + 4096))%Z
    /\ (forall mp ms, vm_maps VM = [(mp, ms)] ->
          (bv_unsigned a + 69632 <= bv_unsigned mp \/ bv_unsigned mp + bv_unsigned ms <= bv_unsigned a)%Z).
  Proof using path Htid Hbrk Hplen.
    intros hint VM a HV Hg. pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi.
    destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
    destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hce & Hrf & Hlive).
    rewrite mV_vmmaps in Hrf. rewrite Hr, Hm, RES_eq in Hrf.
    assert (Hsp : vm_init_sp VM = sp0) by (destruct HV as [-> | [-> | ->]]; reflexivity).
    rewrite mV_vmmaps in Hce. unfold alloc_top in Hce. rewrite Hsp, stack_max_size_val in Hce.
    unfold page_size in Hal. pose proof (u64_range a) as Ha.
    assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
    pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 12288) Hrf ltac:(cbn [In app]; tauto)) as D1.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 155648) (Z_to_bv 64 204800) Hrf ltac:(cbn [In app]; tauto)) as D4.
    pose proof (region_free_In _ _ _ mp ms Hrf ltac:(cbn [In app]; tauto)) as D5.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 77824) (Z_to_bv 64 73728) Hrf ltac:(cbn [In app]; tauto)) as D2.
    pose proof (region_free_In _ _ _ (Z_to_bv 64 151552) (Z_to_bv 64 4096) Hrf ltac:(cbn [In app]; tauto)) as D3.
    rewrite Hn in D2, D3. rewrite !u64_lit in D2 by lia. rewrite !u64_lit in D3 by lia.
    rewrite Hn in D1, D4, D5. rewrite !u64_lit in D1 by lia. rewrite !u64_lit in D4 by lia.
    assert (Ha4096 : (4096 <= bv_unsigned a)%Z).
    { destruct (proj1 (Z.mod_divide (bv_unsigned a) 4096 ltac:(lia)) Hal) as [q Hq]. lia. }
    pose proof (u64_range mp).
    split.
    2:{ intros mp' ms' Hm'. rewrite Hm in Hm'. injection Hm' as <- <-. exact D5. }
    destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; rewrite ?Hms1, ?Hmp in D5; repeat split; lia.
  Qed.

  Lemma w65_mid : forall vals R M VM,
    exitG_branch ->
    length vals = 72%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv ->
    vals_ev vals 70 = brk -> vals_ev vals 5 = tid ->
    regs_ok (ENVv vals) srM R -> know_ok RSEGS (ENVv vals) M knM -> vm_mid VM -> SI M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1cabc) M (seg_rom RSEGS)) (modelV VM))
               (t_alt2 (t_die msg_oom fs0) K).
  Proof using Hvsp Htid Hbrk Hplen SI_step.
    intros vals R M VM EXIT HL P0 P2 P70 P5 HR HK HV HSI.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    (* [comment removed for export] *)
    run_block_keep scr0 72%nat. si_block HSI R M.
    (* [comment removed for export] *)
    eapply (rz_mmap_anon RSEGS _ _ _ (modelV VM) ECALLW 69632).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - apply vm_mid_grant_exists. exact HV.
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x1dba8 + 4)%Z with 0x1dbac%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR2 end.
      eapply (w65_oomN vals); [exact HL | exact P0 | exact HR2 | exact HK].
    - (* [comment removed for export] *)
      intros a Hg. rewrite v_addi_pc4 by lia. change (0x1dba8 + 4)%Z with 0x1dbac%Z.
      change (page_round_up_Z 69632) with 69632%Z in Hg |- *.
      destruct (vm_mid_grant _ VM a HV Hg) as ((Gal & Glo & Ghi & Gdj) & Gsep).
      (* [comment removed for export] *)
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [a] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [a] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      clear HR HK.
      set (vals2 := vals ++ [a]) in *.
      assert (HL2 : length vals2 = 73%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
      assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
      assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      assert (Q72 : vals_ev vals2 72 = a).
      { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
      clearbody vals2. clear HL P0 P2 P70 P5 vals. rename HL2 into HL.
      change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2, HK2.
      pose proof (regs_set_a0 (ENVv vals2) _ _ a gx HR2 ltac:(cbn [edenot gx ev ENV]; exact Q72)) as HR. clear HR2.
      (* [comment removed for export] *)
      lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
        assert (HK3 : know_ok RSEGS (ENVv vals2) Mc knG00) end.
      { unfold knG00. apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]]]].
        - apply kalign_intro; [lia|]. cbn [edenot gx ev ENV]. rewrite Q72. exact Gal.
        - apply krange_intro. cbn [edenot gx ev ENV]. rewrite Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot bx gx ev ENV]. rewrite Q70, Q72. lia.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot bx gx ev ENV]. rewrite Q0, Q72. lia. }
      clear HK2.
      pose proof (xfer_zfill RSEGS (ENVv vals2) _ knG00 gx 0 a 69632 HK3
                    ltac:(unfold estart; cbn [a_base a_off edenot gx ev ENV]; rewrite Q72; lia)
                    ltac:(lia) ltac:(lia)) as HK.
      clear HK3.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knG0 in HK by (vm_compute; reflexivity) end.
      apply (w65_G vals2 _ _ _ EXIT HL Q0 Q2 Q70 Q5 HR HK).
      3:{ si_fill HSI. }
      2:{ rewrite Q72. destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
          unfold w65_vm, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [vm_reserved vm_limit vm_maps]. rewrite Hr, Hl, Hm.
          split; [reflexivity|]. split; [reflexivity|].
          specialize (Gsep mp ms Hm). pose proof (u64_range mp).
          destruct Hms as [[Hms1 ->] | [Hms1 Hmp]].
          - left. split; [rewrite <- (Z_to_bv_bv_unsigned 64 ms), Hms1; reflexivity | lia].
          - right. split; [rewrite <- (Z_to_bv_bv_unsigned 64 ms), Hms1, <- (Z_to_bv_bv_unsigned 64 mp), Hmp; reflexivity | lia]. }
      (* [comment removed for export] *)
      rewrite Q72. destruct (vm_mid_shape VM HV) as (Hr & Hl & mp & ms & Hm & Hms).
      unfold vm_pre, mmap_model. rewrite ?with_vmmaps_vm, ?mV_vmmaps. cbn [vm_reserved vm_limit vm_maps vm_noaccess vm_start_brk vm_brk vm_init_sp].
      assert (Hsp0 : vm_init_sp VM = sp0) by (destruct HV as [-> | [-> | ->]]; reflexivity).
      rewrite Hr, Hl, Hm, Hsp0.
      assert (Hn : bv_unsigned (Z_to_bv 64 69632) = 69632%Z) by (apply u64_lit; lia).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply map_has_head|].
      pose proof (u64_range mp) as Hmpr. pose proof (Gsep mp ms Hm) as Gsp.
      split.
      { constructor; [cbn [fst snd]; rewrite ?Hn; lia|]. constructor; [|constructor].
        cbn [fst snd]. destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; lia. }
      split; [cbn; lia|].
      split; [cbn [live_bytes]; rewrite Hn; lia|].
      split.
      { exists (mp, ms). split; [cbn [In]; tauto|]. cbn [fst snd].
        split; [intros Emp; apply (f_equal bv_unsigned) in Emp; destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; lia|].
        destruct Hms as [[Hms1 ->] | [Hms1 Hmp]]; lia. }
      (* [comment removed for export] *)
      constructor; [|constructor; [constructor | constructor]].
      constructor; [|constructor]. unfold UbTargetPre.iv_disjoint. cbn [fst snd]. rewrite Hn. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac guard_tail EXIT HL P0 P1 P2 P70 P5 VMX HSI Rn Mn :=
    run_blockW_keep scr0 71%nat; si_block HSI Rn Mn;
    lazymatch goal with
    | HR' : regs_ok _ ?sr ?R', HK' : know_ok _ _ ?M' ?kn |- _ =>
      (* [comment removed for export] *)
      pose proof (env_app_regs _ [getr R' 10] _ sr R' ltac:(rewrite HL; vm_compute; reflexivity) HR') as HR2;
      pose proof (env_app_know RSEGS _ [getr R' 10] _ M' kn ltac:(rewrite HL; vm_compute; reflexivity) HK') as HK2;
      clear HR' HK';
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst _ _ _ _) _) _ =>
        lazymatch type of HL with length ?vals = _ =>
        set (vals2 := vals ++ [getr R' 10]) in *;
        assert (HL2 : length vals2 = 72%nat) by (subst vals2; rewrite length_app, HL; reflexivity);
        assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
        assert (Q2 : vals_ev vals2 2 = p1 sp0 a0s path envv) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2);
        assert (Q70 : vals_ev vals2 70 = brk) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70);
        assert (Q5 : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5);
        assert (Q71 : vals_ev vals2 71 = getr R' 10)
          by (subst vals2; rewrite <- HL; rewrite <- (Nat.add_0_r (length vals)); rewrite vals_ev_app_r; reflexivity);
        change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENVv vals2) in HR2, HK2;
        pose proof (regs_ok_set_have (ENVv vals2) _ R' 10 _ (EVar 71) HR2 eq_refl
                      ltac:(cbn [edenot ev ENV]; exact Q71) ltac:(discriminate)) as HR3;
        clear HR2;
        lazymatch type of HR3 with regs_ok _ ?sr3 _ => replace sr3 with srM in HR3 by (vm_compute; reflexivity) end;
        pose proof (know_ok_sub RSEGS (ENVv vals2) M' kn knM ltac:(vm_compute; reflexivity) HK2) as HK3;
        clear HK2;
        apply (w65_mid vals2 R' M' VMX EXIT HL2 Q0 Q2 Q70 Q5 HR3 HK3); [ | exact HSI ]
        end
      end
    end.

  Theorem brk_ok_worldV : exitG_branch -> brk_ok_entry (t_alt2 (t_die msg_oom fs0) K).
  Proof using Hvsp Htid Hbrk Hplen SI_step.
    intros EXIT vals R M HL P0 P70 P1 P2 P5 HR HK HSI0.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (brk_lo brk Hbrk) as Blo. pose proof (brk_hi path brk Hbrk Hplen) as Bhi. pose proof (brk_al brk Hbrk) as Bal.
    assert (HSI : SI (zfill brk (Z_to_bv 64 8192) M)) by si_fill HSI0. clear HSI0.
    (* [comment removed for export] *)
    pose proof (regs_set_a0 (ENVv vals) _ _ (Z_to_bv 64 (bv_unsigned brk + 8192)) (EAlu ALU_ADD bx (ELit 8192)) HR
                  ltac:(rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot bx ev ENV];
                        rewrite P70; reflexivity)) as HR1. clear HR.
    lazymatch type of HR1 with regs_ok _ ?sr _ => replace sr with srW0 in HR1 by (vm_compute; reflexivity) end.
    (* [comment removed for export] *)
    pose proof (xfer_zfill RSEGS (ENVv vals) M knD2 bx 0 brk 8192 HK
                  ltac:(unfold estart; cbn [a_base a_off edenot bx ev ENV]; rewrite P70; lia) ltac:(lia)
                  ltac:(pose proof (u64_range brk); lia)) as HK0. clear HK.
    pose proof (kderive_all_sound RSEGS (ENVv vals) _ _ knW0 HK0 ltac:(vm_compute; reflexivity)) as HK1. clear HK0.
    rename HR1 into HR. rename HK1 into HK.
    change (mkModelC fdsV (mkVmMapsFull RES [(brk, Z_to_bv 64 8192)] [] brk (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                    stdin0 fs0 None (Some tid) None) with (modelV VMk).
    (* [comment removed for export] *)
    run_block_keep scr0 71%nat. si_block HSI R M.
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_alt3 (t_alt2 (t_die msg_oom fs0) K) (t_alt2 (t_die msg_oom fs0) K) (t_alt2 (t_die msg_oom fs0) K)));
      [ | apply t_alt3_idem ].
    eapply (rz_mmap_fixed_noaccess RSEGS _ _ _ (modelV VMk) ECALLW brk 4096).
    - vm_compute. reflexivity.
    - apply is_ecall_ECALLW.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). cbn [edenot bx ev ENV]. exact P70.
    - exact Bal.
    - lia.
    - regv HR (11 : reg). reflexivity.
    - lia.
    - change (page_round_up_Z 4096) with 4096%Z. rewrite mV_vmmaps. unfold alloc_top. cbn [VMk vm_init_sp]. rewrite stack_max_size_val.
      pose proof (proj1 Hvsp). unfold sp_window_lo in *. lia.
    - regv HR (12 : reg). reflexivity.
    - regv HR (13 : reg). reflexivity.
    - regv HR (14 : reg). apply bv_eq. reflexivity.
    - regv HR (15 : reg). reflexivity.
    - rewrite mV_vmmaps. cbn [VMk vm_reserved]. apply region_free_above_top. rewrite rtop. lia.
    - rewrite mV_vmmaps. cbn [VMk vm_maps]. change (page_round_up_Z 4096) with 4096%Z.
      apply map_contains_head; rewrite ?u64_lit by lia; lia.
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x1dba8 + 4)%Z with 0x1dbac%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR1 end.
      clear HR. rename HR1 into HR.
      guard_tail EXIT HL P0 P1 P2 P70 P5 VMk HSI R M. left. reflexivity.
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x1dba8 + 4)%Z with 0x1dbac%Z.
      change (page_round_up_Z 4096) with 4096%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc brk bx HR ltac:(cbn [edenot bx ev ENV]; exact P70)) as HR1 end.
      clear HR. rename HR1 into HR.
      lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
        pose proof (xfer_unfill RSEGS E Mc kn bx 0 brk 4096 HK
                      ltac:(unfold estart; cbn [a_base a_off edenot bx ev ENV]; rewrite P70; lia) ltac:(lia)
                      ltac:(pose proof (u64_range brk); lia)) as HK1 end.
      clear HK. rename HK1 into HK.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knU in HK by (vm_compute; reflexivity) end.
      change (fixed_noaccess_model brk (Z_to_bv 64 4096) (modelV VMk)) with (modelV VMo).
      lazymatch type of HK with know_ok _ _ ?Mc _ => assert (HSI2 : SI Mc) by si_fill HSI end.
      clear HSI. rename HSI2 into HSI.
      guard_tail EXIT HL P0 P1 P2 P70 P5 VMo HSI R M. right. left. reflexivity.
    - (* [comment removed for export] *)
      intros e He. assert (e = ENOMEM) as -> by (destruct He as [<-|[]]; reflexivity).
      rewrite v_addi_pc4 by lia. change (0x1dba8 + 4)%Z with 0x1dbac%Z.
      change (page_round_up_Z 4096) with 4096%Z.
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_set_a0 E sr Rc (errno_ret ENOMEM) ENOMEMv HR ltac:(apply bv_eq; reflexivity)) as HR1 end.
      clear HR. rename HR1 into HR.
      lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
        pose proof (xfer_unfill RSEGS E Mc kn bx 0 brk 4096 HK
                      ltac:(unfold estart; cbn [a_base a_off edenot bx ev ENV]; rewrite P70; lia) ltac:(lia)
                      ltac:(pose proof (u64_range brk); lia)) as HK1 end.
      clear HK. rename HK1 into HK.
      lazymatch type of HK with know_ok _ _ _ ?kn => replace kn with knU in HK by (vm_compute; reflexivity) end.
      (* [comment removed for export] *)
      rewrite fixed_destroyed_model_simple by reflexivity. rewrite mV_vmmaps.
      cbn [VMk vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit].
      rewrite maps_subtract_cons, !maps_subtract_nil, app_nil_r.
      rewrite (u64_lit 4096) by lia.
      rewrite iv_subtract_prefix by (rewrite ?u64_lit by lia; lia).
      rewrite u64_lit by lia.
      replace (bv_unsigned brk + 8192 - (bv_unsigned brk + 4096))%Z with 4096%Z by lia.
      change (with_vmmaps (mkVmMapsFull RES [(Z_to_bv 64 (bv_unsigned brk + 4096), Z_to_bv 64 4096)] [] brk
                       (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0) (modelV VMk)) with (modelV VMd).
      lazymatch type of HK with know_ok _ _ ?Mc _ => assert (HSI2 : SI Mc) by si_fill HSI end.
      clear HSI. rename HSI2 into HSI.
      guard_tail EXIT HL P0 P1 P2 P70 P5 VMd HSI R M. right. right. reflexivity.
  Qed.
End World.

(* [comment removed for export] *)
Theorem brk_ok_world_g {AMB : Amb} sp0 a0s path envv tid mem0 brk mbase fs0 stdin0
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) fd3 K :
  exitG_branch sp0 a0s path envv tid brk fs0 stdin0 fd3 (above_eq sp0 mem0) K ->
  brk_ok_branch_g sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 fd3 (t_alt2 (t_die msg_oom fs0) K).
Proof.
  intros EXIT. exact (brk_ok_worldV sp0 a0s path envv tid brk mbase fs0 stdin0 Hvsp Htid Hbrk Hplen fd3
                        (above_eq sp0 mem0) (above_eq_step sp0 mem0) K EXIT).
Qed.

Theorem brk_ok_world {AMB : Amb} sp0 a0s path envv tid mem0 brk mbase fs0 stdin0
  (Hvsp : valid_sp sp0) (Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z) (Hbrk : valid_brk RSEGS brk)
  (Hplen : (length path <= 4095)%nat) K :
  exitG_branch sp0 a0s path envv tid brk fs0 stdin0 (FdFile path (Z_to_bv 64 0)) (above_eq sp0 mem0) K ->
  brk_ok_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 (t_alt2 (t_die msg_oom fs0) K).
Proof. exact (brk_ok_world_g sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 Hvsp Htid Hbrk Hplen (FdFile path (Z_to_bv 64 0)) K). Qed.
