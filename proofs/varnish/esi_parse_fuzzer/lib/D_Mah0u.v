(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm D_Li6dm Spec LibWbxd RefNodes D_Exvwg D_Stqgu D_Exit RefMocc D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MemSplit Frame SymAux D_Wamxh.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh.

Module D_MainA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 RefMocc D_Manqc D_Li6dm.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import SX2. Import SX2S.

(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition kn_exec : list kentry := kn_main.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS : list Z := [0x2ac54; 0x2b058; 0x2b41c; 0x2ab58; 0x22fc4; 0x22e84; 0x18000; 0x2299c; 0x25d58]%Z.

Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].

Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x17b64 sr_main [] kn_exec 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_exec.
Definition logA : list sentry := Eval vm_compute in s_log (fst (fst rA)).

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x2b77c srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition logB : list sentry := Eval vm_compute in s_log (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End D_MainA.

Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); timeout 8 (Zify.zify; xlia zchecker).   (* timeout-ok: fast tier: hot2_mid's caller catches its failure and runs zify; xlia without it *)
Local Ltac hot_lia_prev := first [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
Local Ltac hot_lia_rest := first [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= first [ solve [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.hplen_pre; hot_lia_rest ] | hot_lia_rest ].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIM {BW : BWorld} : Z := bw_lim.
(* [comment removed for export] *)

Section Pilot.
  Context {AMB : Amb}.
  Context {BW : BWorld}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
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
  Variable PX : (word -> option byte) -> Prop.
  Hypothesis PX_frame : forall M M' : word -> option byte,
    (forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z -> M' x = M x) -> PX M -> PX M'.
  Hypothesis PX0 : PX mem0.

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path rdraw)).

  (* [comment removed for export] *)
  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  (* [comment removed for export] *)
  Definition model0 : Model :=
    with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; path] envv fs0 stdin0)).
  (* [comment removed for export] *)
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition model1g (fd3 : FdEntry) : Model :=
    mkModelC (fds1g fd3) (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk LIM mbase sp0) stdin0 fs0 None (Some tid) None.
  Definition fds1 : list (word * FdEntry) := fds1g (FdFile path (Z_to_bv 64 0)).
  Definition model1 : Model := model1g (FdFile path (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk LIM mbase sp0.
  Proof. intros. reflexivity. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma m0_fds : m_fds model0 = fds0.
  Proof. reflexivity. Qed.
  Lemma m0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Hplen Hvsp"] Lemma above_sp0_block : forall vals log M,
    vals_ev vals 0 = sp0 -> log_below_b 0 0x63000 log = true -> above_sp0 M ->
    above_sp0 (mem_denot (ENV vals) M log).
  Proof.
    intros vals log M P0 Hb HA a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    rewrite (mem_denot_above (ENV vals) M log 0%nat 0x63000 a Hb); [apply HA; exact Ha | | |];
      cbn [ev ENV]; rewrite ?P0; lia.
  Qed.

  Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3.
  Proof. exact (alloc_fd_init _ _ _). Qed.
  Lemma fd_lookup_fds0_3 : fd_lookup fds0 (Z_to_bv 64 3) = None.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac refresh_above vals P0 HA :=
    lazymatch type of HA with above_sp0 ?Mo =>
      lazymatch goal with EQ : ?Mn = mem_denot _ Mo ?log |- _ =>
        let HA' := fresh "HA" in
        pose proof (above_sp0_block vals log Mo P0 ltac:(vm_compute; reflexivity) HA) as HA';
        rewrite <- EQ in HA'; clear HA EQ; rename HA' into HA
      end
    end.
  (* [comment removed for export] *)
  Ltac name_state R M :=
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into R; rename Mn into M end.

  #[using="Hva a0s"] Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.
  (* [comment removed for export] *)
  #[using="Hva a0s"] Lemma path_noslash : path_has_slash path = false /\ path_eqb path dotdot_path = false.
  Proof.
    destruct Hva as (_ & _ & _ & _ & Hs). cbn [tl] in Hs. inversion Hs as [|x l Hx Hl]; subst. exact Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b77c) M (seg_rom RSEGS)) model0) KA.

  (* [comment removed for export] *)
  Definition after_open_g (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 38%nat -> vals_ev vals 0 = sp0 ->
      vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv -> vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srB R -> know_ok RSEGS (ENV vals) M knB -> above_sp0 M -> PX M ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x22fc4) M (seg_rom RSEGS)) (model1g fd3)) KB.
  Definition after_open_branch (KB : TSet) : Prop := after_open_g (FdFile path (Z_to_bv 64 0)) KB.

  (* [comment removed for export] *)
  Lemma logA_cov : log_covered [(SA (EVar 0) (-8388608), 8388608%Z)] (s_log (fst (fst rA))) = true /\ log_w18 (s_log (fst (fst rA))) = true.
  Proof. vm_compute. split; reflexivity. Qed.
  Lemma logB_cov : log_covered [(SA (EVar 0) (-8388608), 8388608%Z)] (s_log (fst (fst rB))) = true /\ log_w18 (s_log (fst (fst rB))) = true.
  Proof. vm_compute. split; reflexivity. Qed.
  #[using="PX_frame Hplen Hvsp"] Lemma PX_block : forall vals M log,
    vals_ev vals 0 = sp0 ->
    log_covered [(SA (EVar 0) (-8388608), 8388608%Z)] log = true -> log_w18 log = true ->
    PX M -> PX (mem_denot (ENV vals) M log).
  Proof.
    intros vals M log P0 C W HP. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    apply (PX_frame M); [| exact HP]. intros x Hx.
    apply (mem_denot_frame (ENV vals) M [(SA (EVar 0) (-8388608), 8388608%Z)] log x C W).
    - intros r Hr. destruct Hr as [<-|[]]. unfold flat, estart. cbn [fst snd a_base a_off edenot ev ENV]. rewrite P0. lia.
    - cbn [map rdenot fst snd outside]. unfold in_rng, estart. cbn [a_base a_off edenot ev ENV]. rewrite P0.
      rewrite u_small by lia. split; [lia| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="PX_frame Hplen Hvsp"] Lemma main_segB_g : forall fd3 KB vals R M,
    after_open_g fd3 KB ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 ->
    vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv -> vals_ev vals 5 = tid ->
    regs_ok (ENV vals) srB0 R -> know_ok RSEGS (ENV vals) M knA -> above_sp0 M -> PX M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2b77c) M (seg_rom RSEGS)) (model1g fd3)) KB.
  Proof.
    intros fd3 KB vals R M HKB HL P0 P1 P2 P5t HR HK HA HP.
    run_block_keep scr0 38%nat.
    lazymatch goal with EQ : ?Mn = mem_denot _ ?Mo ?lg |- _ =>
      assert (HP' : PX Mn) by (rewrite EQ; apply (PX_block vals Mo lg P0 (proj1 logB_cov) (proj2 logB_cov) HP)) end.
    refresh_above vals P0 HA.
    eapply (HKB vals); try eassumption.
  Qed.

  #[using="PX0 PX_frame Hplen Hpnd Hpne Hfile ME Htid Hvsp Hve Hva fdata"] Lemma main_seg1 : forall KA KB,
    open_err_branch KA -> after_open_branch KB ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x17b64) mem0 (seg_rom RSEGS)) model0)
               (t_alt2 KA KB).
  Proof.
    intros KA KB HKA HKB.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s path envv rdraw tid regs0 mem0 Hvsp Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
    change (E0 sp0 a0s path envv rdraw tid regs0) with (ENV (vals0 sp0 a0s path envv tid regs0)) in HR, HK.
    set (vals := vals0 sp0 a0s path envv tid regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    destruct (main_str sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. unfold p1. rewrite (rdn_mem_denot_above RSEGS (ENV vals) mem0 _ 0%nat 0x63000);
        [exact Sr | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia
        | pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)); lia]. }
    (* [comment removed for export] *)
    eapply (rz_openat_file RSEGS _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - (* [comment removed for export] *) rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - (* [comment removed for export] *) split; [exact Hplen|]. split; [apply path_nonul|].
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. exact Sr'.
    - exact Hpne.
    - exact Hpnd.
    - exact (proj2 path_noslash).
    - exact (proj1 path_noslash).
    - rewrite m0_fs. exact Hfile.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x2b778 + 4)%Z with 0x2b77c%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path rdraw))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x63000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x2b778 + 4)%Z with 0x2b77c%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0)
        with (model1g (FdFile path (Z_to_bv 64 0))).
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      assert (HA : above_sp0 M).
      { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x63000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
      lazymatch goal with EQ : ?Mn = mem_denot _ ?Mo ?lg |- _ =>
        assert (HP : PX Mn) by (rewrite EQ; apply (PX_block vals Mo lg P0 (proj1 logA_cov) (proj2 logA_cov) PX0)) end.
      eapply (main_segB_g (FdFile path (Z_to_bv 64 0)) KB vals); try eassumption.
  Qed.

End Pilot.
