(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.   (* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld RzMuo9c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg.

Module ShapeEF.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SimInv.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim BWorld ShapeAlg.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.BWorld OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef_w :
  forall (BWs BWt : BWorld)
         source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (BW:=BWs) source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (BW:=BWt) target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  never_excused (BW:=BWs) source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) ->
  never_excused (BW:=BWt) target_segs (init_config target_segs apc aph asp abrk amb arnd alim inp) ->
  error_free (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros BWs BWt source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget Hns Hnt.
  split; [| split].
  - cbn. exact (realizes_no_error (BW:=BWs) source_segs _ T Hsource Hns).
  - cbn. exact (realizes_no_error (BW:=BWt) target_segs _ T Htarget Hnt).
  - intro tr. cbn.
    rewrite (realizes_obs_iff (BW:=BWs) source_segs _ T Hsource Hns tr).
    rewrite (realizes_obs_iff (BW:=BWt) target_segs _ T Htarget Hnt tr).
    reflexivity.
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (BW:=bw_pinned) source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (BW:=bw_pinned) target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  exact (shape_strong_equiv_ef_w bw_pinned bw_pinned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T inp Hsource Htarget
           (never_excused_pinned _ _) (never_excused_pinned _ _)).
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef_budgets :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (BW:=bw_premise rlim) source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (BW:=bw_pinned) target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  ~ reaches_budget_refused_cfg source_segs ACFG (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) ->
  error_free (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget Hprem.
  exact (shape_strong_equiv_ef_w (bw_premise rlim) bw_pinned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T inp Hsource Htarget
           (never_excused_of_premise rlim _ _ Hprem) (never_excused_pinned _ _)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End ShapeEF.

From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Spec LibIface V_Img0 D_TrLoop.

Module D_Hdqio.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm D_Li6dm Spec LibWbxd RefNodes D_Exvwg D_Stqgu D_Exit RefMocc RefPl89 D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MemSplit D_Kn21w D_Knp98.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Wamxh SymAux.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_TrRuns.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_TrTail.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_TrVals D_TrTail.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Knp98 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Reu44 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrRuns OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrTail.D_TrLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrVals OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrTail.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
(* [comment removed for export] *)
Lemma natz_len_range : forall (A : Type) (l : list A) (a b : nat) (za zb : Z),
  Z.of_nat a = za -> Z.of_nat b = zb -> (a <= length l <= b)%nat -> (za <= Z.of_nat (length l) <= zb)%Z.
Proof. intros A l a b za zb <- <- H. split; apply Nat2Z.inj_le; apply H. Qed.
Lemma natz_len_le : forall (A : Type) (l : list A) (b : nat) (zb : Z), Z.of_nat b = zb -> (length l <= b)%nat -> (Z.of_nat (length l) <= zb)%Z.
Proof. intros A l b zb <- H. apply Nat2Z.inj_le; exact H. Qed.
(* [comment removed for export] *)
Lemma natz_len_le_4095 : forall (A : Type) (l : list A), (length l <= 4095)%nat -> (Z.of_nat (length l) <= 4095)%Z.
Proof. intros A l H. exact (natz_len_le A l 4095%nat 4095%Z (@eq_refl Z 4095%Z) H). Qed.
Local Ltac natz_pos_lit p := lazymatch p with xH => idtac | xO ?q => natz_pos_lit q | xI ?q => natz_pos_lit q end.
Local Ltac natz_z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => natz_pos_lit p end.   (* [comment removed for export] *)
Local Ltac natz_kl :=
  repeat match goal with
  | H : (@length ?A ?l <= 4095)%nat |- _ =>
      let Hz := fresh "KLz" in pose proof (natz_len_le_4095 A l H) as Hz; clear H
  | H : (?a <= @length ?A ?l <= ?b)%nat |- _ =>
      let za := eval vm_compute in (Z.of_nat a) in let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit za; natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_range A l a b za zb (@eq_refl Z za) (@eq_refl Z zb) H) as Hz; clear H
  | H : (@length ?A ?l <= ?b)%nat |- _ =>
      let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_le A l b zb (@eq_refl Z zb) H) as Hz; clear H
  end.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Zifyk6b.   (* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= natz_kl; OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Zifyk6b.zon_hook.
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition valsT (vals : list word) (R : bvmap 5 word) (v6 v7 v8 v9 v10 v11 v12 : word) (b L capk owned v calls : Z) : list word :=
  [vals_ev vals 0; vals_ev vals 1; vals_ev vals 2; vals_ev vals 3; vals_ev vals 4; vals_ev vals 5;
   v6; v7; v8; v9; v10; v11; v12;
   getr R 22; getr R 23; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;   (* [comment removed for export] *)
   Z_to_bv 64 b; Z_to_bv 64 L; Z_to_bv 64 capk; Z_to_bv 64 owned; Z_to_bv 64 v; Z_to_bv 64 calls;
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] ++ junk_vals R.

Lemma valsT_length : forall vals R v6 v7 v8 v9 v10 v11 v12 b L capk owned v calls,
  length (valsT vals R v6 v7 v8 v9 v10 v11 v12 b L capk owned v calls) = 70%nat.
Proof. intros. unfold valsT. rewrite length_app, junk_vals_length. reflexivity. Qed.

(* [comment removed for export] *)
Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x123f3) 31 = Some msg_short.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10ce2) 31 = Some msg_overrun.
Proof. vm_compute. reflexivity. Qed.

Lemma resS_eq : stdio_call 70 srS1 knS1 = Some resS. Proof. vm_compute. reflexivity. Qed.
Lemma resV_eq : stdio_call 70 srV1 knV1 = Some resV. Proof. vm_compute. reflexivity. Qed.
Lemma knTL_vars22 : kn_vars_lt 22 knTL = true. Proof. vm_compute. reflexivity. Qed.
Lemma knS2p_incl : kn_incl knTL knS2p = true. Proof. vm_compute. reflexivity. Qed.
Lemma knV2p_incl : kn_incl knTL knV2p = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RS_leaf : list sregion := [(SA (EVar 0) (-8388608), 8388608%Z); (SA (ELit 0) 0x315a8, 232%Z)].
Lemma logS1_cov : log_covered RS_leaf (s_log (fst (fst rS1))) = true /\ log_w18 (s_log (fst (fst rS1))) = true.
Proof. vm_compute. split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma logV1_cov : log_covered RS_leaf (s_log (fst (fst rV1))) = true /\ log_w18 (s_log (fst (fst rV1))) = true.
Proof. vm_compute. split; reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Section Leaves.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variable fs0 : Fs.
  Variable data : list byte.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis Hplen : (length path <= 4095)%nat.

  Let L : Z := Z.of_nat (length data).
  Definition dbyte (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
  Definition cfg : Z := cfgv (dbyte 0) (dbyte 1).

  #[using="L"] Lemma dbyte_range : forall i, (0 <= dbyte i < 256)%Z.
  Proof. clear Hvsp Htid Hfile Hplen. intros i. unfold dbyte. pose proof (bv_unsigned_in_range 8 (nth i data (Z_to_bv 8 0))) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

  Lemma u64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros. apply u_small. assumption. Qed.

  #[using="L Hplen Hvsp data"] Lemma sr_h_ok : forall vals R,
    length vals = 70%nat -> vals_ev vals 0 = sp0 -> junk_at vals R -> pins_main sp0 (p1 sp0 a0s path envv) R ->
    vals_ev vals 2 = p1 sp0 a0s path envv ->
    getr R 9 = vals_ev vals 20 -> getr R 19 = vals_ev vals 21 -> getr R 21 = vals_ev vals 22 ->
    getr R 22 = vals_ev vals 13 -> getr R 23 = vals_ev vals 14 ->
    regs_ok (ENV a0s path rdraw vals) sr_h R.
  Proof.
    intros vals R HL V0 HJ [P2 P3 P4 P8 P18 P20 P24 P25 P26 P27] V2 P9 P19 P21 P22 P23.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_h all_regs];
      try (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
             change (edenot (ENV a0s path rdraw vals) (EVar n)) with (vals_ev vals n);
             first [ let i := eval vm_compute in (n - 38)%nat in
                     etransitivity; [| symmetry; exact (HJ i ltac:(lia))]; f_equal; apply bv_eq; reflexivity
                   | exact P9 | exact P19 | exact P21 | exact P22 | exact P23 | rewrite V2; exact P18 ] end).
    - apply getr_zero.
    - rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. change (vals_ev vals 0) with (vals_ev vals 0). rewrite V0, P2. f_equal; lia.
    - exact P3.
    - exact P4.
    - exact P8.
    - exact P20.
    - exact P24.
    - exact P25.
    - exact P26.
    - exact P27.
  Qed.

  #[using="L Hplen data"] Lemma knH_ok : forall vals M b Lv,
    know_ok RSEGS (ENV a0s path rdraw vals) M knD ->
    vals_ev vals 20 = Z_to_bv 64 b -> (4096 <= b)%Z -> (b <= 0x7fffff800000)%Z ->
    vals_ev vals 21 = Z_to_bv 64 Lv -> (0 <= Lv <= 0x4000000)%Z ->
    know_ok RSEGS (ENV a0s path rdraw vals) M knH.
  Proof.
    intros vals M b Lv HK V20 Hb1 Hb2 V21 HL. unfold knH. apply know_ok_app; [exact HK|].
    constructor; [|constructor; [|constructor]]; apply krange_intro; cbn [edenot ev ENV].
    - rewrite V20, u64 by lia. lia.
    - rewrite V21, u64 by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition VT (vals : list word) (R : bvmap 5 word) (k : nat) (b : Z) (calls : Z) : list word :=
    valsT vals R (rd8 true (dbyte 1)) (rd8 false (dbyte 0)) (rd8 false (dbyte (Z.to_nat cfg + 3))) (rd8 false (dbyte (Z.to_nat cfg + 2)))
          (rd8 false (dbyte (Z.to_nat cfg + 4))) (rd8 false (dbyte (Z.to_nat cfg + 5))) (rd8 false (dbyte 2)) b L (cap k) 0 0 calls.

  #[using="Hplen HCEIL Hvsp"] Lemma hdr_setup : forall k b vals R M md A calls,
    hdr_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A ->
    let V := VT vals R k b calls in
    base_ok sp0 a0s path envv tid V /\ junk_at V R
    /\ regs_ok (ENV a0s path rdraw V) sr_h R /\ know_ok RSEGS (ENV a0s path rdraw V) M knH
    /\ vals_ev V 20 = Z_to_bv 64 b /\ vals_ev V 21 = Z_to_bv 64 L /\ vals_ev V 22 = Z_to_bv 64 (cap k)
    /\ vals_ev V 6 = rd8 true (dbyte 1) /\ vals_ev V 7 = rd8 false (dbyte 0) /\ vals_ev V 12 = rd8 false (dbyte 2)
    /\ vals_ev V 25 = Z_to_bv 64 calls.
  Proof.
    intros k b vals R M md A calls ST V.
    pose proof ST as [HB HJ HP HK HA S1 S3 S5 S6 S7 AI0 MI BUF MD]. (first [ pose proof (HB) as dR_1; dand5 dR_1 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof BUF as [LIVE ONLY DS DATA Hk Hlen HlenL].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_2; dand4 dR_2 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    pose proof (cap_range path data Hplen k Hk) as Hcap.
    assert (HLV : length V = 70%nat) by (subst V; apply valsT_length).
    assert (E0 : vals_ev V 0 = sp0) by (subst V; cbn; exact V0).
    assert (E2 : vals_ev V 2 = p1 sp0 a0s path envv) by (subst V; cbn; exact V2).
    assert (HJV : junk_at V R) by (subst V; unfold valsT; apply junk_at_app; reflexivity).
    assert (E20 : vals_ev V 20 = Z_to_bv 64 b) by reflexivity.
    assert (E21 : vals_ev V 21 = Z_to_bv 64 L) by reflexivity.
    assert (E22 : vals_ev V 22 = Z_to_bv 64 (cap k)) by reflexivity.
    split; [|split; [exact HJV|split; [|split; [|OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity]]]].
    - split; [exact HLV|]. subst V. cbn. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
    - apply (sr_h_ok V R HLV E0 HJV HP E2); rewrite ?E20, ?E21, ?E22; try assumption; subst V; reflexivity.
    - apply (knH_ok V M b L); rewrite ?E20, ?E21; try reflexivity; try lia.
      apply (know_ok_agree RSEGS 6 (ENV a0s path rdraw vals)); [| exact knD_vars | exact HK].
      split; [|reflexivity]. intros i Hi. subst V.
      destruct i as [|[|[|[|[|[|i]]]]]]; [reflexivity .. | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac hdl_index x l i :=
    lazymatch l with
    | x :: _ => i
    | _ :: ?r => hdl_index x r constr:(S i)
    end.
  Ltac hdl_in_tab :=
    lazymatch goal with
    | |- In ?x ?l =>
        let l' := eval red in l in
        let i := hdl_index x l' constr:(O) in
        exact (@nth_error_In _ l i x eq_refl)
    end.
  #[using="Htid mem0 tid sp0"] Lemma know_pieces_S : forall E M, know_ok RSEGS E M knS2 -> know_ok RSEGS E M knS2p.
  Proof.
    intros E M HK. unfold knS2p. change (know_ok RSEGS E M (knS2 ++ kimg_pieces TAIL_PIECES)).
    apply know_ok_app; [exact HK|]. unfold TAIL_PIECES.
    change (kimg_pieces ?l) with
      (kimg_pieces [(0x10000, 0x315a8)]%Z ++ (kimg_pieces [(0x31690, 0x31698); (0x31780, 0x317b0)]%Z
       ++ (kimg_pieces [(0x317b1, 0x317f9)]%Z ++ (kimg_pieces [(0x417f9, 0x41800); (0x41801, 0x41804); (0x41805, 0x41830); (0x41840, 0x42088)]%Z
       ++ (kimg_pieces [(0x42170, 0x62160)]%Z ++ (kimg_pieces [(0x62198, 0x621a8); (0x622c8, 0x623c8)]%Z
       ++ kimg_pieces [(0x62804, 0x62858); (0x62c58, 0x63000)]%Z)))))).
    repeat apply know_ok_app.
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x10000 0x315b0); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x31634 0x317b0); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x317b1 0x317f9); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x417f9 0x42088); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x42170 0x62160); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].   (* [comment removed for export] *)
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x62198 0x623c8); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x62804 0x63000); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
  Qed.

  #[using="Hplen Htid HCEIL Hvsp"] Theorem hdr_short : forall k b vals R M md A,
    hdr_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A -> (L < cap k)%Z -> (L < 6)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17c60) M (seg_rom RSEGS)) md) (t_die msg_short fs0).
  Proof.
    intros k b vals R M md A ST HLc HL6.
    (first [ pose proof ((hdr_setup k b vals R M md A 1 ST)) as dR_3; dand11 dR_3 as HB HJ HR HK V20 V21 V22 V6 V7 V12 V25 | destruct (hdr_setup k b vals R M md A 1 ST) as (HB & HJ & HR & HK & V20 & V21 & V22 & V6 & V7 & V12 & V25) ]).
    set (V := VT vals R k b 1) in *.
    pose proof ST as [HB0 _ HP _ HA S1 S3 S5 S6 S7 AI0 MI BUF MD]. pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof BUF as [LIVE ONLY DS DATA Hk Hlen HlenL].
    (first [ pose proof (HB) as dR_4; dand5 dR_4 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof (cap_range path data Hplen k Hk) as Hcap.
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_5; dand4 dR_5 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    clear HJ HP.
    (* [comment removed for export] *)
    run_block_gen FUEL_X STOPS_X (SCR [true] [] []) 6%nat true.
    { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z; lia. }
    rename EQM into EQM1.
    unfold t_die, W.
    apply (stdio_call_sound_frame V (blobs_ev (blobs0 a0s path rdraw)) srS1 knS1 R0 M0 md resS [] msg_short
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n srS1 knS1) HL) resS_eq));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resS];
      change (Z.of_nat (length msg_short)) with 31%Z; change (Z.of_nat (@length byte [])) with 0%Z.
    - cbn [edenot]. lit_u. lia.
    - cbn [edenot]. lia.
    - cbn [edenot]. lit_u. reflexivity.
    - lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0.
      lit_u. rewrite u_small by lia. lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0.
      lit_u. lit_u. rewrite u_small by lia. lia.
    - cbn [edenot]. lit_u. lit_u. lia.
    - reflexivity.
    - cbn [edenot]. change (length msg_short) with 31%nat.
      rewrite (kimg_rdn RSEGS _ _ knS1 ltac:(let i := kidx knS1 (is_kimg_cov 0x123f3 31) in exact i) _ _ 0x123f3 31 HK eq_refl) by (cbn; lia).
      apply msg_short_img.
    - exact Mfd2.
    - exact Mh.
    - exact Mlz.
    - apply t_exit_has_nil.
    - clear HR HK. intros R1 M1 HR HK SWP.
      change (sc_sr resS) with srS2_0 in HR. change (sc_kn resS) with knS2_0 in HK.
      rewrite ?HL in HR, HK.
      set (vals1 := V ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 102%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (AG1 : forall i, (i < 70)%nat -> vals_ev vals1 i = vals_ev V i) by (intros i Hi; subst vals1; apply vals_ev_app_l; rewrite HL; exact Hi).
      change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path rdraw))) with (ENV a0s path rdraw vals1) in HR, HK.
      (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [] [] []) 102%nat true.
      cbn [mem_denot] in EQM. subst M2.
      (* [comment removed for export] *)
      assert (W1 : ainv A M1 md /\ Mem.mem_inv RSEGS M1).
      { pose proof (mem_denot_frame_mod (ENV a0s path rdraw V) M RS_leaf (s_log (fst (fst rS1))) (proj1 logS1_cov) (proj2 logS1_cov)) as FM.
        assert (RF : regions_flat (ENV a0s path rdraw V) RS_leaf).
        { intros r Hr. unfold RS_leaf in Hr. destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]; rewrite ?V0; try lia.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
        specialize (FM RF).
        replace (mem_denot (ENV a0s path rdraw V) M (s_log (fst (fst rS1)))) with M0 in FM by (rewrite EQM1; reflexivity).
        destruct FM as [AGm Gm].
        destruct SWP as [AGs Gs _ _ _].
        rewrite edenot_add_lit in AGs. unfold adenot, v_addi in AGs. cbn [a_base a_off edenot ev ENV] in AGs. rewrite V0, u64 in AGs by lia.
        apply (drv_client sp0 A M M1 md SPlo ltac:(lia) AI0 MI); [| eapply mem_grows_trans; [exact Gm| exact Gs]].
        intros x N1 N2 N3. rewrite AGs by lia. apply AGm.
        unfold RS_leaf. cbn [map rdenot fst snd outside]. unfold in_rng, estart. cbn [a_base a_off edenot ev ENV]. rewrite V0.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite !u64 by lia. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
      destruct W1 as [AI1 MI1].
      set (valsX := rebase vals1 24 (Z_to_bv 64 2) R2).
      assert (HLX : (NB <= length vals1)%nat) by (rewrite HL1; unfold NB; lia).
      assert (AGX : forall j, (j < NB)%nat -> j <> 24%nat -> vals_ev valsX j = vals_ev V j).
      { intros j Hj Hne. subst valsX. rewrite rebase_lt by (assumption || (unfold NB; lia)). apply AG1. unfold NB in Hj. lia. }
      apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (exit_code 2) (m_fs md)))).
      2:{ rewrite Mfs. apply t_emit_W_nil. apply t_exit_has_nil. }
      apply (tail_exit sp0 a0s path envv rdraw tid Hvsp HCEIL valsX R2 M1 md A b (cap k) 2 (Z_to_bv 64 0x62850) (Z_to_bv 64 0) [] false).   (* [comment removed for export] *)
      + split; [apply rebase_length; [exact HLX| unfold NB; lia]|]. rewrite !AGX by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      + apply rebase_junk; [exact HLX| unfold NB; lia].
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite AG1, V0 by lia. f_equal; lia.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + rewrite AGX by (unfold NB; lia). exact V20.
      + subst valsX. apply rebase_at; [exact HLX| unfold NB; lia].
      + lia.
      + regv HR (8%bv : reg). reflexivity.
      + regv HR (9%bv : reg). cbn [edenot ev ENV]. rewrite AG1 by lia. exact V20.
      + apply (know_ok_agree RSEGS 22 (ENV a0s path rdraw vals1)).
        * split; [|reflexivity]. intros i Hi. cbn [ev ENV]. subst valsX. rewrite rebase_lt by (assumption || (unfold NB; lia)). reflexivity.
        * exact knTL_vars22.
        * apply (know_ok_incl RSEGS _ M1 knTL knS2p knS2p_incl). apply know_pieces_S. exact HK.
      + exact AI1.
      + exact LIVE.
      + exact MI1.
      + unfold file_clean. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; krd_solve HK.
      + unfold atexit_st. krd_solve HK.
      + left. split; [reflexivity|]. exists (Z_to_bv 64 0), (Z_to_bv 64 0). unfold file_clean. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; krd_solve HK.
  Qed.
  #[using="Htid mem0 tid sp0"] Lemma know_pieces_V : forall E M, know_ok RSEGS E M knV2 -> know_ok RSEGS E M knV2p.
  Proof.
    intros E M HK. unfold knV2p. change (know_ok RSEGS E M (knV2 ++ kimg_pieces TAIL_PIECES)).
    apply know_ok_app; [exact HK|]. unfold TAIL_PIECES.
    change (kimg_pieces ?l) with
      (kimg_pieces [(0x10000, 0x315a8)]%Z ++ (kimg_pieces [(0x31690, 0x31698); (0x31780, 0x317b0)]%Z
       ++ (kimg_pieces [(0x317b1, 0x317f9)]%Z ++ (kimg_pieces [(0x417f9, 0x41800); (0x41801, 0x41804); (0x41805, 0x41830); (0x41840, 0x42088)]%Z
       ++ (kimg_pieces [(0x42170, 0x62160)]%Z ++ (kimg_pieces [(0x62198, 0x621a8); (0x622c8, 0x623c8)]%Z
       ++ kimg_pieces [(0x62804, 0x62858); (0x62c58, 0x63000)]%Z)))))).
    repeat apply know_ok_app.
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x10000 0x315b0); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x31634 0x317b0); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x317b1 0x317f9); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x417f9 0x42088); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x42170 0x62160); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].   (* [comment removed for export] *)
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x62198 0x623c8); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x62804 0x63000); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
  Qed.

  #[using="Hplen Htid HCEIL Hvsp"] Theorem hdr_overrun : forall k b vals R M md A,
    hdr_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A -> (L < cap k)%Z -> (6 <= L)%Z -> (L < 6 + cfg)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17c60) M (seg_rom RSEGS)) md) (t_die msg_overrun fs0).
  Proof.
    intros k b vals R M md A ST HLc HL6 HLcfg. pose proof (cfgv_range (dbyte 0) (dbyte 1)) as Hcfg. fold cfg in Hcfg.
    pose proof (dbyte_range 0) as B0. pose proof (dbyte_range 1) as B1.
    (first [ pose proof ((hdr_setup k b vals R M md A 1 ST)) as dR_6; dand11 dR_6 as HB HJ HR HK V20 V21 V22 V6 V7 V12 V25 | destruct (hdr_setup k b vals R M md A 1 ST) as (HB & HJ & HR & HK & V20 & V21 & V22 & V6 & V7 & V12 & V25) ]).
    set (V := VT vals R k b 1) in *.
    pose proof ST as [HB0 _ HP _ HA S1 S3 S5 S6 S7 AI0 MI BUF MD]. pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof BUF as [LIVE ONLY DS DATA Hk Hlen HlenL].
    (first [ pose proof (HB) as dR_7; dand5 dR_7 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof (cap_range path data Hplen k Hk) as Hcap.
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_8; dand4 dR_8 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    clear HJ HP.
    (* [comment removed for export] *)
    run_block_gen FUEL_X STOPS_X (SCR [false; true] [] []) 6%nat true.
    { cbn [sc_denot].
      change (branch_taken BC_LTU (vals_ev V 21) (alu64 ALU_ADD (cfgF (vals_ev V 6) (vals_ev V 7)) (Z_to_bv 64 6)) = true).
      rewrite V21, V6, V7, cfgF_val by lia. fold cfg. rewrite alu_add_Z.
      apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_lt. lia. }
    { cbn [sc_denot]. exists [nth 0 data (Z_to_bv 8 0)]. split.
      - unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V20. apply rdn1_of. rewrite u64 by lia. rewrite (DATA 0%Z) by lia. reflexivity.
      - cbn [edenot ev ENV]. rewrite V7. unfold rd8, dbyte. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    { cbn [sc_denot]. exists [nth 1 data (Z_to_bv 8 0)]. split.
      - unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V20. apply rdn1_of. rewrite u64 by lia. rewrite (DATA 1%Z) by lia. reflexivity.
      - cbn [edenot ev ENV]. rewrite V6. unfold rd8, dbyte. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z_false; lia. }
    rename EQM into EQM1.
    unfold t_die, W.
    apply (stdio_call_sound_frame V (blobs_ev (blobs0 a0s path rdraw)) srV1 knV1 R0 M0 md resV [] msg_overrun
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n srV1 knV1) HL) resV_eq));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resV];
      change (Z.of_nat (length msg_overrun)) with 31%Z; change (Z.of_nat (@length byte [])) with 0%Z.
    - cbn [edenot]. lit_u. lia.
    - cbn [edenot]. lia.
    - cbn [edenot]. lit_u. reflexivity.
    - lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0.
      lit_u. rewrite u_small by lia. lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0.
      lit_u. lit_u. rewrite u_small by lia. lia.
    - cbn [edenot]. lit_u. lit_u. lia.
    - reflexivity.
    - cbn [edenot]. change (length msg_overrun) with 31%nat.
      rewrite (kimg_rdn RSEGS _ _ knV1 ltac:(let i := kidx knV1 (is_kimg_cov 0x10ce2 31) in exact i) _ _ 0x10ce2 31 HK eq_refl) by (cbn; lia).
      apply msg_overrun_img.
    - exact Mfd2.
    - exact Mh.
    - exact Mlz.
    - apply t_exit_has_nil.
    - clear HR HK. intros R1 M1 HR HK SWP.
      change (sc_sr resV) with srV2_0 in HR. change (sc_kn resV) with knV2_0 in HK.
      rewrite ?HL in HR, HK.
      set (vals1 := V ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 102%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (AG1 : forall i, (i < 70)%nat -> vals_ev vals1 i = vals_ev V i) by (intros i Hi; subst vals1; apply vals_ev_app_l; rewrite HL; exact Hi).
      change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path rdraw))) with (ENV a0s path rdraw vals1) in HR, HK.
      (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [] [] []) 102%nat true.
      cbn [mem_denot] in EQM. subst M2.
      (* [comment removed for export] *)
      assert (W1 : ainv A M1 md /\ Mem.mem_inv RSEGS M1).
      { pose proof (mem_denot_frame_mod (ENV a0s path rdraw V) M RS_leaf (s_log (fst (fst rV1))) (proj1 logV1_cov) (proj2 logV1_cov)) as FM.
        assert (RF : regions_flat (ENV a0s path rdraw V) RS_leaf).
        { intros r Hr. unfold RS_leaf in Hr. destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]; rewrite ?V0; try lia.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
        specialize (FM RF).
        replace (mem_denot (ENV a0s path rdraw V) M (s_log (fst (fst rV1)))) with M0 in FM by (rewrite EQM1; reflexivity).
        destruct FM as [AGm Gm].
        destruct SWP as [AGs Gs _ _ _].
        rewrite edenot_add_lit in AGs. unfold adenot, v_addi in AGs. cbn [a_base a_off edenot ev ENV] in AGs. rewrite V0, u64 in AGs by lia.
        apply (drv_client sp0 A M M1 md SPlo ltac:(lia) AI0 MI); [| eapply mem_grows_trans; [exact Gm| exact Gs]].
        intros x N1 N2 N3. rewrite AGs by lia. apply AGm.
        unfold RS_leaf. cbn [map rdenot fst snd outside]. unfold in_rng, estart. cbn [a_base a_off edenot ev ENV]. rewrite V0.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite !u64 by lia. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
      destruct W1 as [AI1 MI1].
      set (valsX := rebase vals1 24 (Z_to_bv 64 2) R2).
      assert (HLX : (NB <= length vals1)%nat) by (rewrite HL1; unfold NB; lia).
      assert (AGX : forall j, (j < NB)%nat -> j <> 24%nat -> vals_ev valsX j = vals_ev V j).
      { intros j Hj Hne. subst valsX. rewrite rebase_lt by (assumption || (unfold NB; lia)). apply AG1. unfold NB in Hj. lia. }
      apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (exit_code 2) (m_fs md)))).
      2:{ rewrite Mfs. apply t_emit_W_nil. apply t_exit_has_nil. }
      apply (tail_exit sp0 a0s path envv rdraw tid Hvsp HCEIL valsX R2 M1 md A b (cap k) 2 (Z_to_bv 64 0x62850) (Z_to_bv 64 0) [] false).   (* [comment removed for export] *)
      + split; [apply rebase_length; [exact HLX| unfold NB; lia]|]. rewrite !AGX by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      + apply rebase_junk; [exact HLX| unfold NB; lia].
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite AG1, V0 by lia. f_equal; lia.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + rewrite AGX by (unfold NB; lia). exact V20.
      + subst valsX. apply rebase_at; [exact HLX| unfold NB; lia].
      + lia.
      + regv HR (8%bv : reg). reflexivity.
      + regv HR (9%bv : reg). cbn [edenot ev ENV]. rewrite AG1 by lia. exact V20.
      + apply (know_ok_agree RSEGS 22 (ENV a0s path rdraw vals1)).
        * split; [|reflexivity]. intros i Hi. cbn [ev ENV]. subst valsX. rewrite rebase_lt by (assumption || (unfold NB; lia)). reflexivity.
        * exact knTL_vars22.
        * apply (know_ok_incl RSEGS _ M1 knTL knV2p knV2p_incl). apply know_pieces_V. exact HK.
      + exact AI1.
      + exact LIVE.
      + exact MI1.
      + unfold file_clean. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; krd_solve HK.
      + unfold atexit_st. krd_solve HK.
      + left. split; [reflexivity|]. exists (Z_to_bv 64 0), (Z_to_bv 64 0). unfold file_clean. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; krd_solve HK.
  Qed.
End Leaves.
End D_Hdqio.

Module D_Header.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm D_Li6dm Spec LibWbxd RefNodes D_Exvwg D_Stqgu D_Exit RefMocc RefPl89 D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MemSplit D_Kn21w D_Knp98.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Wamxh SymAux.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Me92w.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Opzpl.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_TrRuns.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_TrTail.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_TrVals.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Stfzw.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_TrTail D_TrLoop.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require LibIface.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Knp98 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Reu44 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_MkStep OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Loop OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Me92w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Opzpl.D_Memcpy OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrRuns OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrTail.D_TrLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrVals OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stfzw.D_Trk7v OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrTail OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrLoop OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.D_Hdqio OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibIface.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); timeout 8 (Zify.zify; xlia zchecker).   (* timeout-ok: fast tier: hot2_mid's caller catches its failure and runs zify; xlia without it *)
Local Ltac hot_lia_prev := first [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dl_first | tryif OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then first [ hot2_mid | Zify.zify; xlia zchecker ] else first [ solve [OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Zify.zify; xlia zchecker] | hot2_mid | Zify.zify; xlia zchecker ] ].
Local Ltac hot_lia_rest := first [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= first [ solve [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.hplen_pre; hot_lia_rest ] | hot_lia_rest ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac mem_side := cbn; first [ (let E := fresh "E" in intros E; discriminate E) | solve [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ exact I | reflexivity ] ] | solve [ repeat first [ left; reflexivity | right ] ] | tauto ].
Local Ltac mem_hyp Hr := cbn in Hr; first [ solve [ repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); first [ discriminate Hr | destruct Hr ] ] | intuition discriminate ].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma knL_vars22b : kn_vars_lt 22 knL = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma knL_knTm : kn_incl knL knTm = true. Proof. vm_compute. reflexivity. Qed.
Lemma knL_knT : kn_incl knL knT = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knT_iw : nat := Eval vm_compute in match kindex (is_kwr_cov (EVar 0) (-8388608) 8388608) knT 0 with Some i => i | None => 0%nat end.
Lemma knT_win : nth_error knT knT_iw = Some (KWr (SA (EVar 0) (-8388608)) 8388608). Proof. vm_compute. reflexivity. Qed.
Lemma knTm_heap_incl : kn_incl knTm (kn_keep2 knTm RS_heap []) = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition kimg_is (lo hi : Z) (e : kentry) : bool := match e with KImg l h => Z.eqb l lo && Z.eqb h hi | _ => false end.
Lemma kimg_in_b : forall lo hi (L : list kentry), existsb (kimg_is lo hi) L = true -> In (KImg lo hi) L.
Proof.
  intros lo hi L H. apply existsb_exists in H as [e [Hin He]]. destruct e; try discriminate He. cbn [kimg_is] in He.
  apply andb_prop in He as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst. exact Hin.
Qed.
(* [comment removed for export] *)
Lemma knT_of_mm : forall E M, know_ok RSEGS E M (kn_afterX rHmm knH) -> know_ok RSEGS E M knT.
Proof.
  intros E M HK. unfold knT. change (know_ok RSEGS E M (knT0 ++ kimg_pieces TR_PIECES)).
  apply know_ok_app; [exact HK|]. unfold TR_PIECES.
  change (kimg_pieces ?l) with
    (kimg_pieces [(0x10000, 0x31698); (0x10000, 0x315a8); (0x31690, 0x31698); (0x31780, 0x317b0)]%Z
     ++ (kimg_pieces [(0x41801, 0x41804); (0x41805, 0x41830); (0x41840, 0x42088)]%Z ++ kimg_pieces [(0x62804, 0x62858); (0x62c58, 0x63000)]%Z)).
  repeat apply know_ok_app.
  - eapply (know_ok_kimg_pieces RSEGS E M _ 0x10000 0x317b0); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia].
  - eapply (know_ok_kimg_pieces RSEGS E M _ 0x41801 0x42088); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia].
  - eapply (know_ok_kimg_pieces RSEGS E M _ 0x62804 0x63000); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia].
Qed.

Ltac knT_of r :=
  intros E M HK;
  apply (know_ok_incl RSEGS E M knT (kn_afterX r knH ++ kimg_pieces TR_PIECES) ltac:(vm_compute; reflexivity));
  apply know_ok_app; [exact HK|]; unfold TR_PIECES;
  change (kimg_pieces ?l) with
    (kimg_pieces [(0x10000, 0x31698); (0x10000, 0x315a8); (0x31690, 0x31698); (0x31780, 0x317b0)]%Z
     ++ (kimg_pieces [(0x41801, 0x41804); (0x41805, 0x41830); (0x41840, 0x42088)]%Z ++ kimg_pieces [(0x62804, 0x62858); (0x62c58, 0x63000)]%Z));
  repeat apply know_ok_app;
  [ eapply (know_ok_kimg_pieces RSEGS E M _ 0x10000 0x317b0); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia]
  | eapply (know_ok_kimg_pieces RSEGS E M _ 0x41801 0x42088); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia]
  | eapply (know_ok_kimg_pieces RSEGS E M _ 0x62804 0x63000); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia] ].

Lemma knT_of_zm : forall E M, know_ok RSEGS E M (kn_afterX rHzm knH) -> know_ok RSEGS E M knT.
Proof. knT_of rHzm. Qed.
Lemma knT_of_mz : forall E M, know_ok RSEGS E M (kn_afterX rHmz knH) -> know_ok RSEGS E M knT.
Proof. knT_of rHmz. Qed.
Lemma knT_of_zz : forall E M, know_ok RSEGS E M (kn_afterX rHzz knH) -> know_ok RSEGS E M knT.
Proof. knT_of rHzz. Qed.

(* [comment removed for export] *)
Definition RS_hdr : list sregion := [(SA (EVar 0) (-8388608), 8388608%Z); (SA (ELit 0) 0x41800, 1%Z);
  (SA (ELit 0) 0x621a8, 4%Z); (SA (ELit 0) 0x621b0, 8%Z); (SA (ELit 0) 0x621c0, 8%Z); (SA (ELit 0) 0x622c0, 8%Z)].
Lemma logH_cov : forall r, In r [rHmm; rHzm; rHmz; rHzz] ->
  log_covered RS_hdr (s_log (fst (fst r))) = true /\ log_w18 (s_log (fst (fst r))) = true.
Proof. intros r Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; (split; [vm_compute; reflexivity| vm_compute; reflexivity]). Qed.

(* [comment removed for export] *)
Lemma know_knTm_heap : forall E M M',
  know_ok RSEGS E M knTm -> (0x7fff80000000 <= bv_unsigned (ev E 0))%Z ->
  (forall x : word, out_heap (ev E 0) x -> M' x = M x) -> mem_grows M M' -> know_ok RSEGS E M' knTm.
Proof.
  intros E M M' HK Hsp OUT G. apply (know_ok_incl RSEGS E M' knTm _ knTm_heap_incl).
  pose proof (u64_range (ev E 0)) as Hr.
  apply (know_ok_keep2 RSEGS E M M'); [exact HK | | |].
  - unfold RS_heap, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, CSLACK. repeat constructor; unfold estart; cbn [a_base a_off edenot];
      try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  - intros x Hx. apply OUT.
    pose proof (Hx (ELit 0) HEAP_LO (HEAP_HI - HEAP_LO)%Z ltac:(left; reflexivity)) as H1.
    pose proof (Hx (EVar 0) (-8388608 - CSLACK)%Z CSLACK ltac:(right; left; reflexivity)) as H3.
    pose proof (Hx (ELit 0) LOW_LO (LOW_HI - LOW_LO)%Z ltac:(right; right; left; reflexivity)) as H2.
    unfold estart in H1, H2, H3. cbn [a_base a_off edenot] in H1, H2, H3. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in H1, H2.
    unfold CSLACK in H3. unfold out_heap, CSLACK. split; [lia|split; lia].
  - intros x _ Hm. apply G in Hm. exact Hm.
Qed.

Lemma knTm_img : forall E M, know_ok RSEGS E M knTm -> forall i, (0x10000 <= i < 0x317b0)%Z -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M HK i Hi.
  pose proof (know_nth RSEGS _ _ knTm ltac:(let i := kidx knTm (is_kimg_cov 0x31758 1) in exact i) _ HK eq_refl) as K.
  cbn [kentry_ok] in K. (first [ dand3 K as _ _ K | destruct K as (_ & _ & K) ]). apply K. exact Hi.
Qed.
Lemma knT_img : forall E M, know_ok RSEGS E M knT -> forall i, (0x10000 <= i < 0x317b0)%Z -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M HK i Hi.
  pose proof (know_nth RSEGS _ _ knT ltac:(let i := kidx knT (is_kimg_cov 0x31758 1) in exact i) _ HK eq_refl) as K.
  cbn [kentry_ok] in K. (first [ dand3 K as _ _ K | destruct K as (_ & _ & K) ]). apply K. exact Hi.
Qed.

Section Header.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variable fs0 : Fs.
  Variable data : list byte.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* [comment removed for export] *)
  Variable limg : (word -> option byte) -> Prop.
  Hypothesis limg_intro : forall m, Mem.mem_inv RSEGS m ->
    (forall i, (0x30270 <= i < 0x31580)%Z -> m (Z_to_bv 64 i) = None) -> limg m.
  Hypothesis LIBOK : lib_call_ok (LLP limg limg_intro).

  Let L : Z := Z.of_nat (length data).
  Definition cfg : Z := D_Hdqio.cfg data.
  Definition plen : Z := (L - 6 - cfg)%Z.
  Definition cnt : bool := (128 <=? dbyte data 1)%Z.
  Definition calls : Z := (if cfg =? 0 then 1 else dbyte data 2 mod 4 + 1)%Z.
  Definition payload : list byte := skipn (Z.to_nat (6 + cfg)) data.
  Definition v6 : word := rd8 true (dbyte data 1).
  Definition succ : TSet := t_emit (W 1 (zero_lines (Z.to_nat calls))) (t_exit (exit_code 0) fs0).

  Lemma u64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros. apply u_small. assumption. Qed.
  Lemma cfg_range : (0 <= cfg < 32768)%Z. Proof. unfold cfg, D_Hdqio.cfg. apply cfgv_range. Qed.
  #[using="L Hplen path"] Lemma calls_range : (1 <= calls <= 4)%Z.
  Proof. unfold calls. pose proof (dbyte_range data 2%nat). pose proof (Z.mod_pos_bound (dbyte data 2) 4 ltac:(lia)). destruct (cfg =? 0)%Z; lia. Qed.
  #[using="Hplen path"] Lemma payload_length : (6 + cfg <= L)%Z -> Z.of_nat (length payload) = plen.
  Proof. intros H. unfold payload, plen. rewrite length_skipn. pose proof cfg_range. unfold L in *. lia. Qed.

  (* [comment removed for export] *)
  #[using="LIBOK limg_intro limg Hplen Htid HCEIL Hvsp"] Lemma enter_loop : forall k (j : nat) (b owned aligned : Z) V R M md A,
    (6 + cfg <= L)%Z -> (L < cap k)%Z -> (k <= 10)%nat ->
    ((plen = 0 /\ aligned = 0x41810 /\ owned = 0) \/ (0 < plen /\ aligned = owned))%Z ->
    lp_st sp0 a0s path envv rdraw tid fs0 b (cap k) plen owned aligned payload v6 true (S j) 0 V R M md A ->
    (j <= 3)%nat ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17eec) M (seg_rom RSEGS)) md)
             (t_emit (W 1 (zero_lines (S j))) (t_exit (exit_code 0) fs0)).
  Proof.
    intros k j b owned aligned V R M md A HcL HLc Hk Hal ST Hj.
    pose proof (cap_range path data Hplen k Hk) as Hcap. pose proof cfg_range as Hcfg.
    change (zero_lines (S j)) with ([Z_to_bv 8 48; Z_to_bv 8 10] ++ zero_lines j).
    eapply rz_conseq; [| apply t_emit_W_app].
    unfold W at 1. cbn [map].
    apply (tr_entry sp0 a0s path envv rdraw tid Hvsp HCEIL Htid fs0 limg limg_intro LIBOK _ (cap k) plen owned aligned payload v6
             (payload_length HcL) ltac:(unfold plen; lia) Hal j V R M md A _ ST ltac:(lia) (t_emit_has_nil _ _)).
    intros R' M' md' A' ST' INCB'.
    apply (tr_exit sp0 a0s path envv rdraw tid Hvsp HCEIL fs0 _ (cap k) plen owned aligned payload v6 Hal ltac:(unfold plen; lia)
             j V R' M' md' A' (branch_taken BC_LT v6 (Z_to_bv 64 0)) ST' INCB' ltac:(lia) eq_refl).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Vals.
    Variables (V : list word) (b : Z).
    Hypothesis V6 : vals_ev V 6 = rd8 true (dbyte data 1).
    Hypothesis V7 : vals_ev V 7 = rd8 false (dbyte data 0).
    Hypothesis V20 : vals_ev V 20 = Z_to_bv 64 b.
    Hypothesis V21 : vals_ev V 21 = Z_to_bv 64 L.
    Hypothesis Hb : (4096 <= b)%Z /\ (b + 65536 <= 0x7fffff800000)%Z.   (* [comment removed for export] *)
    Hypothesis HL6 : (6 + cfg <= L)%Z /\ (L < 2 ^ 26)%Z.

    #[using="V7 V6 L Hplen"] Lemma cfgX_ev : edenot (ENV a0s path rdraw V) cfgX = Z_to_bv 64 cfg.
    Proof.
      pose proof (dbyte_range data 0). pose proof (dbyte_range data 1).
      unfold ENV. rewrite cfgX_F, V6, V7, cfgF_val by lia. reflexivity.
    Qed.
    #[using="V20 V7 V6 L Hplen"] Lemma baseX_ev : edenot (ENV a0s path rdraw V) (EAlu ALU_ADD (EVar 20) cfgX) = Z_to_bv 64 (b + cfg).
    Proof. change (edenot _ _) with (alu64 ALU_ADD (vals_ev V 20) (edenot (ENV a0s path rdraw V) cfgX)). rewrite V20, cfgX_ev. apply alu_add_Z. Qed.
    #[using="V20 V7 V6 L Hplen"] Lemma payX_ev : edenot (ENV a0s path rdraw V) payX = Z_to_bv 64 (b + cfg + 6).
    Proof. change (edenot _ _) with (alu64 ALU_ADD (edenot (ENV a0s path rdraw V) (EAlu ALU_ADD (EVar 20) cfgX)) (Z_to_bv 64 6)). rewrite baseX_ev. apply alu_add_Z. Qed.
    #[using="HL6 V21 V7 V6 Hplen"] Lemma plenX_ev : edenot (ENV a0s path rdraw V) plenX = Z_to_bv 64 plen.
    Proof.
      pose proof cfg_range.
      change (edenot _ _) with (alu64 ALU_ADD (alu64 ALU_ADD (vals_ev V 21) (mul_div M_MUL (Z_to_bv 64 (-1)) (edenot (ENV a0s path rdraw V) cfgX))) (Z_to_bv 64 (-6))).
      rewrite V21, cfgX_ev. unfold plen. rewrite plen_val by lia. f_equal. lia.
    Qed.
  End Vals.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac ob_rb0 V20 Vn DATA i :=
    cbn [sc_denot]; exists [nth (Z.to_nat i) data (Z_to_bv 8 0)]; split;
    [ unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV]; rewrite V20; apply rdn1_of; rewrite u64 by lia;
      rewrite (DATA i) by lia; reflexivity
    | cbn [edenot ev ENV]; rewrite Vn; unfold rd8, dbyte; rewrite Z_to_bv_bv_unsigned; reflexivity ].
  (* [comment removed for export] *)
  Ltac use_base BASEV :=
    lazymatch type of BASEV with edenot ?E _ = ?v =>
      match goal with |- context [edenot E (EAlu ALU_ADD (EVar 20) ?t)] =>
        replace (edenot E (EAlu ALU_ADD (EVar 20) t)) with v by (symmetry; exact BASEV) end end.
  Ltac ob_rbc b BASEV Vn DATA j :=
    cbn [sc_denot]; exists [nth (Z.to_nat cfg + j) data (Z_to_bv 8 0)]; split;
    [ unfold adenot, v_addi; cbn [a_base a_off]; use_base BASEV; rewrite u64 by lia; apply rdn1_of;
      match goal with |- ?Mx (Z_to_bv 64 ?a) = _ => replace a with (b + (cfg + Z.of_nat j))%Z by lia end;
      rewrite (DATA (cfg + Z.of_nat j)%Z) by lia; do 2 f_equal; lia
    | cbn [edenot ev ENV]; rewrite Vn; unfold rd8, dbyte; rewrite Z_to_bv_bv_unsigned; reflexivity ].
  Ltac ob_flat BASEV :=
    cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; use_base BASEV;
    change (bv_unsigned (edenot _ (ELit 1))) with 1%Z; rewrite u64 by lia; lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac ob_ldisj V20 :=
    solve [ lazymatch goal with |- sc_denot _ _ _ (SCDisj _ _ (SA (ELit 0) _) _) =>
              cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off edenot ev ENV]; rewrite V20;
              change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; change (bv_unsigned (Z_to_bv 64 1)) with 1%Z;
              try change (bv_unsigned (Z_to_bv 64 4)) with 4%Z; try change (bv_unsigned (Z_to_bv 64 8)) with 8%Z;
              rewrite !u64 by lia; OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia end ].
  Ltac ob_sdisj V20 V0 :=
    solve [ lazymatch goal with |- sc_denot _ _ _ (SCDisj _ _ (SA (EVar 0) _) _) =>
              cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off edenot ev ENV]; rewrite V20, V0;
              change (bv_unsigned (Z_to_bv 64 1)) with 1%Z; change (bv_unsigned (Z_to_bv 64 8)) with 8%Z;
              rewrite !u64 by lia; OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia end ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma knTm_eq : kn_keep2 knT (RS_call (-208) MALLOC_STACK) VICT ++ [kwr_data] = knTm.
  Proof. vm_compute. reflexivity. Qed.
  Lemma know_knTm : forall E M', know_ok RSEGS E M' (kn_keep2 knT (RS_call (-208) MALLOC_STACK) VICT) -> know_ok RSEGS E M' knTm.
  Proof. intros E M' HK. rewrite <- knTm_eq. apply know_ok_app; [exact HK | constructor; [apply kwr_data_ok | constructor]]. Qed.
  Lemma payX_vars : expr_vars_lt 70 payX = true. Proof. vm_compute. reflexivity. Qed.
  Lemma plenX_vars : expr_vars_lt 70 plenX = true. Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="L Hplen HCEIL Hvsp data path sp0"] Lemma blk_client : forall A M M' md p n,
    ainv A M md -> a_live A p = Some n -> Mem.mem_inv RSEGS M ->
    (forall x : word, ~ (p <= bv_unsigned x < p + n)%Z -> M' x = M x) -> mem_grows M M' ->
    ainv A M' md /\ Mem.mem_inv RSEGS M'.
  Proof.
    intros A M M' md p n AI0 LV MI OUT G.
    (first [ pose proof ((as_live_ok A M md p n AI0 LV)) as dR_3; dand7 dR_3 as C0 _ P1 HI LO MP NO | destruct (as_live_ok A M md p n AI0 LV) as (C0 & _ & P1 & HI & LO & MP & NO) ]).
    rewrite HCEIL in HI. cbn [al_image_lo al_image_hi LayoutP0] in LO.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0). pose proof alloc_ceiling_val.
    assert (Hh : m_halted md = None) by (destruct (as_lazy_nil A M md AI0) as [_ X]; exact X).
    assert (OUTZ : forall a, (0 <= a < 2 ^ 64)%Z -> ~ (p <= a < p + n)%Z -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N1. apply OUT; rewrite u64 by lia; assumption. }
    split.
    - apply (as_frame A M M' md md AI0).
      + intros a Ho. pose proof (owned_azone A M md a AI0 Ho) as ZZ. unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in ZZ.
        apply OUTZ; [lia|]. intros Hin. apply (NO (a - p)%Z ltac:(lia)). replace (p + (a - p))%Z with a by lia. exact Ho.
      + intros a Hs. cbn [al_shared LayoutP0] in Hs. unfold p0_shared in Hs. apply OUTZ; lia.
      + intros q c i HL Hi. (first [ pose proof ((as_live_ok A M md q c AI0 HL)) as dR_4; dand7 dR_4 as _ _ _ _ _ MPq _ | destruct (as_live_ok A M md q c AI0 HL) as (_ & _ & _ & _ & _ & MPq & _) ]). apply G. apply MPq. exact Hi.
      + intros a [Ha Hni] Hm. rewrite HCEIL in Ha. unfold in_image in Hni. cbn [al_image_lo al_image_hi LayoutP0] in Hni.
        destruct (Z_lt_le_dec a p) as [L1|L1]; [rewrite OUTZ in Hm by lia; exact Hm|].
        destruct (Z_lt_le_dec a (p + n)) as [L2|L2]; [|rewrite OUTZ in Hm by lia; exact Hm].
        replace a with (p + (a - p))%Z by lia. apply MP. lia.
      + reflexivity.
      + exact Hh.
    - intros x v Hx. destruct (Mem.ro_addr RSEGS x) eqn:RO; [|reflexivity]. exfalso.
      pose proof (proj1 (as_ro_addr_iff (AI:=AI) x) RO) as RA. cbn [al_image_lo al_rw_lo LayoutP0] in RA.
      rewrite OUT in Hx by lia. pose proof (MI x v Hx) as RO'. rewrite RO' in RO. discriminate.
  Qed.

  #[using="LIBOK limg_intro limg Hplen Htid HCEIL Hvsp mem0"] Lemma malloc_part : forall k b V R M md A,
    regs_ok (ENV a0s path rdraw V) sr_m R ->
    know_ok RSEGS (ENV a0s path rdraw V) M knT ->
    base_ok sp0 a0s path envv tid V ->
    vals_ev V 6 = rd8 true (dbyte data 1) -> vals_ev V 7 = rd8 false (dbyte data 0) ->
    vals_ev V 20 = Z_to_bv 64 b -> vals_ev V 21 = Z_to_bv 64 L -> vals_ev V 25 = Z_to_bv 64 calls ->
    ainv A M md -> Mem.mem_inv RSEGS M -> MDcl fs0 md ->
    a_live A b = Some (cap k) -> (a_livebytes A = cap k /\ a_nlive A = 1%Z) ->   (* [comment removed for export] *)
    (forall i, (0 <= i < L)%Z -> M (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))) ->
    (k <= 10)%nat -> (L < cap k)%Z -> (6 + cfg <= L)%Z -> (0 < plen)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x22fc4) M (seg_rom RSEGS)) md) succ.   (* [comment removed for export] *)
  Proof.
    intros k b V R M md A HR HK HB V6 V7 V20 V21 V25 AI0 MI MD LIVE DS DATA Hk HLc HcL Hp.
    (first [ pose proof (HB) as dR_5; dand5 dR_5 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]). pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof (cap_range path data Hplen k Hk) as Hcap. pose proof cfg_range as Hcfg. pose proof calls_range as Hcalls.
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_6; dand4 dR_6 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    pose proof (dbyte_range data 0) as B0. pose proof (dbyte_range data 1) as B1. pose proof (dbyte_range data 2) as B2.
    assert (HLV : (6 + cfg <= L)%Z /\ (L < 2 ^ 26)%Z) by lia.
    pose proof (plenX_ev V V6 V7 V21 HLV) as PLENV. pose proof (payX_ev V b V6 V7 V20) as PAYV.
    assert (Hpl : (0 < plen < 2 ^ 26)%Z) by (unfold plen in *; lia).
    assert (CH : callH V (blobs_ev (blobs0 a0s path rdraw)) sr_m knT plen (-208) 0x17e98).
    { split; rewrite ?HL, ?V0; try reflexivity; try lia.
      - exact PLENV.
      - exists knT_iw. exact knT_win. }
    destruct DS as [LB0 NL0].
    apply (W_malloc_nf V (blobs_ev (blobs0 a0s path rdraw)) sr_m knT R M md A plen (-208) 0x17e98 _ HR HK CH AI0
             (ex_intro _ b (ex_intro _ (cap k) LIVE)) MI ltac:(lia) ltac:(rewrite NREQ_CAP_eq; lia)
             ltac:(rewrite LIVE_MAX_eq, LB0; lia) ltac:(rewrite NLIVE_MAX_eq, NL0; lia)).
    (* [comment removed for export] *)
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 md1 A1 r Hr Hv80 HR HK1 AI1 MI1 MF1 NONE1 LIVE1 OTHER1 LB1 NL1 FR1.
      pose proof (know_knTm _ M1 HK1) as HK. clear HK1.
      assert (Hh1 : m_halted md1 = None) by (destruct (as_lazy_nil A1 M1 md1 AI1) as [_ X]; exact X).
      assert (Hl1 : m_vm_lazy md1 = []) by (destruct (as_lazy_nil A1 M1 md1 AI1) as [X _]; exact X).
      rewrite HL in HR, Hv80. change (sr_post sr_m 70) with srB_0 in HR. change (70 + 10)%nat with 80%nat in Hv80.
      set (vals1 := V ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 102%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (AG1 : forall i, (i < 70)%nat -> vals_ev vals1 i = vals_ev V i) by (intros i Hi; subst vals1; apply vals_ev_app_l; rewrite HL; exact Hi).
      change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path rdraw))) with (ENV a0s path rdraw vals1) in HR, HK.
      (first [ pose proof ((block_range sp0 path data HCEIL Hplen A1 M1 md1 r plen AI1 LIVE1)) as dR_8; dand4 dR_8 as _ Hr16 HrLO HrHI | destruct (block_range sp0 path data HCEIL Hplen A1 M1 md1 r plen AI1 LIVE1) as (_ & Hr16 & HrLO & HrHI) ]). unfold HEAP_LO, LOW_HI in HrLO.
      assert (Hrb : r <> b) by (intros ->; rewrite LIVE in NONE1; discriminate).
      assert (LIVEB1 : a_live A1 b = Some (cap k)) by (rewrite (OTHER1 b ltac:(congruence)); exact LIVE).
      pose proof (as_live_disjoint A1 M1 md1 b (cap k) r plen AI1 LIVEB1 LIVE1 ltac:(congruence)) as DISJ.
      rewrite V0 in FR1.
      assert (DATA1 : forall i, (0 <= i < L)%Z -> M1 (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. rewrite <- (DATA i Hi).
        apply (block_acall sp0 path data Hvsp HCEIL Hplen A A1 M M1 md md1 (-208) MALLOC_STACK nowhere (blk r plen) b (cap k) AI0 AI1 LIVE FR1);
          [unfold MALLOC_STACK; lia | intros j Hj Hv; exact Hv | | lia].
        intros j Hj [_ Hin]. lia. }
      (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [false] [] []) 102%nat true.
      { cbn [sc_denot edenot ev ENV]. rewrite Hv80, bt_eq0_Z by lia. apply Z.eqb_neq. lia. }
      cbn [mem_denot] in EQM. subst M0.
      assert (PAYL : length payload = Z.to_nat plen) by (pose proof (payload_length HcL); lia).
      assert (MCH : mcH M1 (Z_to_bv 64 r) (Z_to_bv 64 (b + cfg + 6)) plen payload).
      { split.
        - lia.
        - exact PAYL.
        - apply rdn_pointwise; [reflexivity | rewrite u64, PAYL by lia; unfold plen in *; lia |].
          intros j Hj. rewrite u64 by lia. rewrite PAYL in Hj.
          replace (b + cfg + 6 + Z.of_nat j)%Z with (b + (6 + cfg + Z.of_nat j))%Z by lia.
          rewrite (DATA1 (6 + cfg + Z.of_nat j)%Z) by (unfold plen in *; lia).
          unfold payload. rewrite nth_skipn. do 2 f_equal. lia.
        - rewrite PAYL. eapply (block_store_ok sp0 path data Hvsp HCEIL Hplen A1 M1 md1 r plen); [exact AI1| exact LIVE1| lia| lia].
        - rewrite !u64 by lia. unfold plen in *. lia.
        - rewrite u64 by lia. unfold plen in *. lia.
        - rewrite u64 by lia. lia. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?RR _ _ _) _) _ => rename RR into R2 end.
      destruct (ref_memcpy M1 (Z_to_bv 64 r) (Z_to_bv 64 (b + cfg + 6)) plen payload (seg_rom RSEGS) MCH R2 (Z_to_bv 64 0x17eac))
        as [R3 [MS KEEPS]].
      { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
      { regv HR (1%bv : reg). reflexivity. }
      { regv HR (10%bv : reg). cbn [edenot ev ENV]. exact Hv80. }
      { regv HR (11%bv : reg). subst vals1. exact (eq_trans (env_app_edenot V (junk_vals R1) (blobs_ev (blobs0 a0s path rdraw)) payX ltac:(rewrite HL; exact payX_vars)) PAYV). }
      { regv HR (12%bv : reg). subst vals1. exact (eq_trans (env_app_edenot V (junk_vals R1) (blobs_ev (blobs0 a0s path rdraw)) plenX ltac:(rewrite HL; exact plenX_vars)) PLENV). }
      replace (Z_to_bv 64 0x2ac54) with (0x2ac54 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh1 | exact Hl1 | exact MS |].
      set (M3 := wbytes M1 (Z_to_bv 64 r) payload) in *.
      assert (OUT3 : forall x : word, ~ (r <= bv_unsigned x < r + plen)%Z -> M3 x = M1 x).
      { intros x Hx. subst M3. apply wbytes_outside; rewrite u64, ?PAYL by lia; unfold in_rng; rewrite ?u64 by lia; lia. }
      assert (IN3 : forall i, (0 <= i < plen)%Z -> M3 (Z_to_bv 64 (r + i)) = Some (nth (Z.to_nat i) payload (Z_to_bv 8 0))).
      { intros i Hi. subst M3. rewrite wbytes_inside by (rewrite ?PAYL, !u64 by lia; lia). rewrite !u64 by lia.
        replace (Z.to_nat (r + i - r)) with (Z.to_nat i) by lia. reflexivity. }
      assert (G3 : mem_grows M1 M3) by (subst M3; apply wbytes_grows).
      assert (HK3 : know_ok RSEGS (ENV a0s path rdraw vals1) M3 knTm).
      { apply (know_knTm_heap _ M1 M3 HK); [cbn [ev ENV]; rewrite ?AG2, ?AG1 by lia; rewrite V0; lia | | exact G3].
        intros x [Hx1 [Hx2 Hx3]]. cbn [ev ENV] in Hx2. rewrite ?AG2, ?AG1 in Hx2 by lia. rewrite V0 in Hx2. apply OUT3. unfold HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, CSLACK in Hx1, Hx2, Hx3. lia. }
      destruct (blk_client A1 M1 M3 md1 r plen AI1 LIVE1 MI1 OUT3 G3) as [AI3 MI3].
      (* [comment removed for export] *)
      destruct (tr_c R3 M3 (seg_rom RSEGS)) as (R4 & MS4 & S9 & S22 & S23 & KEEP4).
      replace (Z_to_bv 64 0x17eac) with (0x17eac : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh1 | exact Hl1 | exact MS4 |].
      replace (0x17eec : word) with (Z_to_bv 64 0x17eec) by (apply bv_eq; reflexivity).
      assert (KR : forall rr : reg, In rr callee_kept -> rr <> 9%bv -> rr <> 22%bv -> rr <> 23%bv -> getr R4 rr = getr R2 rr).
      { intros rr Hin H9 H22 H23. rewrite KEEP4 by assumption. apply KEEPS. exact Hin. }
      set (j := (Z.to_nat calls - 1)%nat).
      replace succ with (t_emit (W 1 (zero_lines (S j))) (t_exit (exit_code 0) fs0)) by (unfold succ; f_equal; f_equal; f_equal; subst j; lia).
      set (valsL := rebase vals1 23 (Z_to_bv 64 r) R4).
      assert (HLX : (NB <= length vals1)%nat) by (rewrite HL1; unfold NB; lia).
      assert (AGX : forall q, (q < NB)%nat -> q <> 23%nat -> vals_ev valsL q = vals_ev V q).
      { intros q Hq Hne. subst valsL. rewrite rebase_lt by (assumption || (unfold NB; lia)). apply AG1. unfold NB in Hq. lia. }
      apply (enter_loop k j b r r valsL R4 M3 md1 A1 HcL HLc Hk ltac:(right; lia)); [| subst j; lia].
      split.
      + split; [apply rebase_length; [exact HLX| unfold NB; lia]|]. rewrite !AGX by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      + rewrite AGX by (unfold NB; lia). exact V6.
      + rewrite AGX by (unfold NB; lia). exact V20.
      + subst valsL. apply rebase_at; [exact HLX| unfold NB; lia].
      + apply (know_ok_agree RSEGS 22 (ENV a0s path rdraw vals1)).
        * split; [|reflexivity]. intros i Hi. cbn [ev ENV]. subst valsL. rewrite rebase_lt by (assumption || (unfold NB; lia)). reflexivity.
        * exact knL_vars22b.
        * apply (know_ok_incl RSEGS _ M3 knL knTm knL_knTm). exact HK3.
      + rewrite KR by mem_side. regv HR (2%bv : reg).
        rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite AG1, V0 by lia. f_equal; lia.
      + rewrite KR by mem_side. regv HR (3%bv : reg). reflexivity.
      + rewrite KR by mem_side. regv HR (4%bv : reg). reflexivity.
      + rewrite KR by mem_side. regv HR (8%bv : reg).
        subst vals1. exact (eq_trans (env_app_edenot V (junk_vals R1) (blobs_ev (blobs0 a0s path rdraw)) plenX ltac:(rewrite HL; exact plenX_vars)) PLENV).
      + rewrite S9. rewrite (KEEPS 18%bv ltac:(mem_side)). regv HR (18%bv : reg). cbn [edenot ev ENV]. exact Hv80.
      + rewrite KR by mem_side. regv HR (18%bv : reg). cbn [edenot ev ENV]. exact Hv80.
      + rewrite KR by mem_side. regv HR (20%bv : reg). reflexivity.
      + rewrite KR by mem_side. regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite AG1 by lia. rewrite V25.
        f_equal. subst j. lia.
      + exact S22.
      + exact S23.
      + exact AI3.
      + exact MI3.
      + (first [ dand4 MF1 as FD _ FS _ | destruct MF1 as (FD & _ & FS & _) ]). split.
        * unfold m_fs. rewrite FS. exact Mfs.
        * unfold m_fds. rewrite FD. exact Mfd1.
        * unfold m_fds. rewrite FD. exact Mfd2.
        * exact Hh1.
        * exact Hl1.
      + exact LIVEB1.
      + right. split; [exact LIVE1| exact IN3].
      + intros i Hi. rewrite OUT3 by (rewrite u64 by lia; lia). apply (knTm_img _ M1 HK). lia.
      + (* [comment removed for export] *)
        rewrite LB1, NL1, LB0, NL0, LIVE_MAX_eq, NLIVE_MAX_eq. unfold LIB_LIVE, LIB_NLIVE. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac hdr_frame r V M M0 EQM V0 AGm Gm :=
    let FM := fresh "FM" in let RF := fresh "RF" in
    pose proof (mem_denot_frame_mod (ENV a0s path rdraw V) M RS_hdr (s_log (fst (fst r)))
                  (proj1 (logH_cov r ltac:(mem_side))) (proj2 (logH_cov r ltac:(mem_side)))) as FM;
    assert (RF : regions_flat (ENV a0s path rdraw V) RS_hdr)
      by (intros rr Hr; unfold RS_hdr in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]; rewrite ?V0;
          first [lia | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia]);
    specialize (FM RF);
    replace (mem_denot (ENV a0s path rdraw V) M (s_log (fst (fst r)))) with M0 in FM by (rewrite EQM; reflexivity);
    destruct FM as [AGm Gm]; clear RF.

  (* [comment removed for export] *)
  #[using="L Hplen Hvsp data"] Lemma outside_hdr : forall V (x : word),
    vals_ev V 0 = sp0 ->
    ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z -> ~ (0x41800 <= bv_unsigned x < 0x622c8)%Z ->
    outside x (map (rdenot (ENV a0s path rdraw V)) RS_hdr).
  Proof.
    intros V x V0 N1 N2. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    unfold RS_hdr. cbn [map rdenot fst snd outside]. unfold in_rng, estart. cbn [a_base a_off edenot ev ENV]. rewrite V0.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite !u64 by lia. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.

  #[using="LIBOK limg_intro limg Hplen Htid HCEIL Hvsp"] Theorem hdr_run : forall k b vals R M md A,
    hdr_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A -> (L < cap k)%Z -> (6 + cfg <= L)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17c60) M (seg_rom RSEGS)) md) succ.   (* [comment removed for export] *)
  Proof.
    intros k b vals R M md A ST HLc HcL.
    (first [ pose proof ((hdr_setup sp0 a0s path envv rdraw tid mem0 fs0 data Hvsp HCEIL Hplen k b vals R M md A calls ST)) as dR_11; dand11 dR_11 as HB HJ HR HK V20 V21 V22 V6 V7 V12 V25 | destruct (hdr_setup sp0 a0s path envv rdraw tid mem0 fs0 data Hvsp HCEIL Hplen k b vals R M md A calls ST)
      as (HB & HJ & HR & HK & V20 & V21 & V22 & V6 & V7 & V12 & V25) ]).
    set (V := VT data vals R k b calls) in *.
    pose proof ST as [HB0 _ HP _ HA S1 S3 S5 S6 S7 AI0 MI BUF MD]. pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof BUF as [LIVE ONLY DS DATA Hk Hlen HlenL].
    (first [ pose proof (HB) as dR_12; dand5 dR_12 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof (cap_range path data Hplen k Hk) as Hcap. pose proof cfg_range as Hcfg. pose proof calls_range as Hcalls.
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_13; dand4 dR_13 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    pose proof (dbyte_range data 0) as B0. pose proof (dbyte_range data 1) as B1. pose proof (dbyte_range data 2) as B2.
    assert (HbV : (4096 <= b)%Z /\ (b + 65536 <= 0x7fffff800000)%Z) by lia.
    assert (HLV : (6 + cfg <= L)%Z /\ (L < 2 ^ 26)%Z) by lia.
    pose proof (baseX_ev V b V6 V7 V20) as BASEV. pose proof (plenX_ev V V6 V7 V21 HLV) as PLENV. pose proof (cfgX_ev V V6 V7) as CFGV.
    assert (V8 : vals_ev V 8 = rd8 false (dbyte data (Z.to_nat cfg + 3))) by reflexivity.
    assert (V9 : vals_ev V 9 = rd8 false (dbyte data (Z.to_nat cfg + 2))) by reflexivity.
    assert (V10 : vals_ev V 10 = rd8 false (dbyte data (Z.to_nat cfg + 4))) by reflexivity.
    assert (V11 : vals_ev V 11 = rd8 false (dbyte data (Z.to_nat cfg + 5))) by reflexivity.
    clear HJ HP.
    destruct (Z.eqb_spec cfg 0) as [Hc0|Hc0]; destruct (Z.eqb_spec plen 0) as [Hp0|Hp0].
    - (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [false; false; true; false] [] []) 6%nat true.
      all: try (ob_sdisj V20 V0).
      { cbn [sc_denot]. change (branch_taken BC_NE (edenot (ENV a0s path rdraw V) plenX) (Z_to_bv 64 0) = false). rewrite PLENV, bt_ne0_Z by (unfold plen; lia). rewrite (proj2 (Z.eqb_eq _ _) Hp0). reflexivity. }
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 0) = true). rewrite CFGV, bt_eq0_Z by lia. rewrite (proj2 (Z.eqb_eq _ _) Hc0). reflexivity. }
      { ob_rbc b BASEV V11 DATA 5%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V10 DATA 4%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V9 DATA 2%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V8 DATA 3%nat. }
      { ob_flat BASEV. }
      { cbn [sc_denot]. change (branch_taken BC_LTU (vals_ev V 21) (alu64 ALU_ADD (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 6)) = false).
        rewrite V21, CFGV, alu_add_Z. apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_ge. lia. }
      { ob_rb0 V20 V7 DATA 0%Z. }
      { ob_rb0 V20 V6 DATA 1%Z. }
      { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z_false; lia. }
      (* [comment removed for export] *)
      pose proof (knT_of_zz _ M0 HK) as HKT.
      hdr_frame rHzz V M M0 EQM V0 AGm Gm.
      assert (W0 : ainv A M0 md /\ Mem.mem_inv RSEGS M0).
      { apply (drv_client sp0 A M M0 md SPlo ltac:(lia) AI0 MI); [| exact Gm]. intros x N1 N2 N3. apply AGm. apply (outside_hdr V x V0); lia. }
      destruct W0 as [AI0' MI0'].
      cbv beta iota.
      replace succ with (t_emit (W 1 (zero_lines 1)) (t_exit (exit_code 0) fs0))
        by (unfold succ, calls; rewrite (proj2 (Z.eqb_eq _ _) Hc0); reflexivity).
      apply (enter_loop k 0 b 0 0x41810 V R0 M0 md A HcL HLc Hk ltac:(left; lia)); [| lia].
      split.
      + exact HB. + exact V6. + exact V20. + reflexivity.
      + apply (know_ok_incl RSEGS _ M0 knL knT knL_knT). exact HKT.
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0. f_equal; lia.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + regv HR (8%bv : reg). exact PLENV.
      + regv HR (9%bv : reg). reflexivity.
      + regv HR (18%bv : reg). reflexivity.
      + regv HR (20%bv : reg). reflexivity.
      + regv HR (21%bv : reg). reflexivity.
      + regv HR (22%bv : reg). reflexivity.
      + regv HR (23%bv : reg). reflexivity.
      + exact AI0'.
      + exact MI0'.
      + split; assumption.
      + exact LIVE.
      + left. exact Hp0.
      + intros i Hi. apply (knT_img _ M0 HKT). lia.
      + (* [comment removed for export] *)
        destruct DS as [LB0 NL0]. rewrite LB0, NL0, Hp0, LIVE_MAX_eq, NLIVE_MAX_eq. unfold LIB_LIVE, LIB_NLIVE. lia.
    - (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [false; false; true; true] [] []) 6%nat true.
      all: try (ob_sdisj V20 V0).
      { cbn [sc_denot]. change (branch_taken BC_NE (edenot (ENV a0s path rdraw V) plenX) (Z_to_bv 64 0) = true). rewrite PLENV, bt_ne0_Z by (unfold plen; lia).
        rewrite (proj2 (Z.eqb_neq _ _) Hp0). reflexivity. }
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 0) = true). rewrite CFGV, bt_eq0_Z by lia. rewrite (proj2 (Z.eqb_eq _ _) Hc0). reflexivity. }
      { ob_rbc b BASEV V11 DATA 5%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V10 DATA 4%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V9 DATA 2%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V8 DATA 3%nat. }
      { ob_flat BASEV. }
      { cbn [sc_denot]. change (branch_taken BC_LTU (vals_ev V 21) (alu64 ALU_ADD (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 6)) = false).
        rewrite V21, CFGV, alu_add_Z. apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_ge. lia. }
      { ob_rb0 V20 V7 DATA 0%Z. }
      { ob_rb0 V20 V6 DATA 1%Z. }
      { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z_false; lia. }
      cbv beta iota.
      pose proof (knT_of_zm _ M0 HK) as HKT.
      hdr_frame rHzm V M M0 EQM V0 AGm Gm.
      assert (W0 : ainv A M0 md /\ Mem.mem_inv RSEGS M0).
      { apply (drv_client sp0 A M M0 md SPlo ltac:(lia) AI0 MI); [| exact Gm]. intros x N1 N2 N3. apply AGm. apply (outside_hdr V x V0); lia. }
      destruct W0 as [AI0' MI0'].
      assert (DATA0 : forall i, (0 <= i < L)%Z -> M0 (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. rewrite AGm; [apply DATA; exact Hi|]. apply (outside_hdr V _ V0); rewrite u64 by lia; lia. }
      apply (malloc_part k b V R0 M0 md A); try assumption; try (unfold plen in *; lia).
      refine (regs_ok_pin _ _ _ (21%bv : reg) (EVar 25) HR _). regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite V25. unfold calls. rewrite (proj2 (Z.eqb_eq _ _) Hc0). reflexivity.
    - (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [false; false; false; true] [] []) 6%nat true.
      all: try (ob_sdisj V20 V0). all: try (ob_ldisj V20).
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) plenX) (Z_to_bv 64 0) = true). rewrite PLENV, bt_eq0_Z by (unfold plen; lia).
        rewrite (proj2 (Z.eqb_eq _ _) Hp0). reflexivity. }
      { ob_rb0 V20 V12 DATA 2%Z. }
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 0) = false). rewrite CFGV, bt_eq0_Z by lia. rewrite (proj2 (Z.eqb_neq _ _) Hc0). reflexivity. }
      { ob_rbc b BASEV V11 DATA 5%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V10 DATA 4%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V9 DATA 2%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V8 DATA 3%nat. }
      { ob_flat BASEV. }
      { cbn [sc_denot]. change (branch_taken BC_LTU (vals_ev V 21) (alu64 ALU_ADD (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 6)) = false).
        rewrite V21, CFGV, alu_add_Z. apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_ge. lia. }
      { ob_rb0 V20 V7 DATA 0%Z. }
      { ob_rb0 V20 V6 DATA 1%Z. }
      { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z_false; lia. }
      pose proof (knT_of_mz _ M0 HK) as HKT.
      hdr_frame rHmz V M M0 EQM V0 AGm Gm.
      assert (W0 : ainv A M0 md /\ Mem.mem_inv RSEGS M0).
      { apply (drv_client sp0 A M M0 md SPlo ltac:(lia) AI0 MI); [| exact Gm]. intros x N1 N2 N3. apply AGm. apply (outside_hdr V x V0); lia. }
      destruct W0 as [AI0' MI0'].
      cbv beta iota.
      set (j := Z.to_nat (dbyte data 2 mod 4)).
      pose proof (Z.mod_pos_bound (dbyte data 2) 4 ltac:(lia)) as Hm4.
      replace succ with (t_emit (W 1 (zero_lines (S j))) (t_exit (exit_code 0) fs0)).
      2:{ unfold succ, calls. rewrite (proj2 (Z.eqb_neq _ _) Hc0). f_equal. f_equal. f_equal. subst j. lia. }
      apply (enter_loop k j b 0 0x41810 V R0 M0 md A HcL HLc Hk ltac:(left; lia)); [| subst j; lia].
      split.
      + exact HB. + exact V6. + exact V20. + reflexivity.
      + apply (know_ok_incl RSEGS _ M0 knL knT knL_knT). exact HKT.
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0. f_equal; lia.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + regv HR (8%bv : reg). exact PLENV.
      + regv HR (9%bv : reg). reflexivity.
      + regv HR (18%bv : reg). reflexivity.
      + regv HR (20%bv : reg). reflexivity.
      + regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite V12, rd8_u by lia. rewrite calls_val by lia. f_equal. subst j. lia.
      + regv HR (22%bv : reg). reflexivity.
      + regv HR (23%bv : reg). reflexivity.
      + exact AI0'.
      + exact MI0'.
      + split; assumption.
      + exact LIVE.
      + left. exact Hp0.
      + intros i Hi. apply (knT_img _ M0 HKT). lia.
      + (* [comment removed for export] *)
        destruct DS as [LB0 NL0]. rewrite LB0, NL0, Hp0, LIVE_MAX_eq, NLIVE_MAX_eq. unfold LIB_LIVE, LIB_NLIVE. lia.
    - (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [false; false; false; false] [] []) 6%nat true.
      all: try (ob_sdisj V20 V0). all: try (ob_ldisj V20).
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) plenX) (Z_to_bv 64 0) = false). rewrite PLENV, bt_eq0_Z by (unfold plen; lia).
        rewrite (proj2 (Z.eqb_neq _ _) Hp0). reflexivity. }
      { ob_rb0 V20 V12 DATA 2%Z. }
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 0) = false). rewrite CFGV, bt_eq0_Z by lia. rewrite (proj2 (Z.eqb_neq _ _) Hc0). reflexivity. }
      { ob_rbc b BASEV V11 DATA 5%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V10 DATA 4%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V9 DATA 2%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V8 DATA 3%nat. }
      { ob_flat BASEV. }
      { cbn [sc_denot]. change (branch_taken BC_LTU (vals_ev V 21) (alu64 ALU_ADD (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 6)) = false).
        rewrite V21, CFGV, alu_add_Z. apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_ge. lia. }
      { ob_rb0 V20 V7 DATA 0%Z. }
      { ob_rb0 V20 V6 DATA 1%Z. }
      { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z_false; lia. }
      cbv beta iota.
      pose proof (knT_of_mm _ M0 HK) as HKT.
      hdr_frame rHmm V M M0 EQM V0 AGm Gm.
      assert (W0 : ainv A M0 md /\ Mem.mem_inv RSEGS M0).
      { apply (drv_client sp0 A M M0 md SPlo ltac:(lia) AI0 MI); [| exact Gm]. intros x N1 N2 N3. apply AGm. apply (outside_hdr V x V0); lia. }
      destruct W0 as [AI0' MI0'].
      assert (DATA0 : forall i, (0 <= i < L)%Z -> M0 (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. rewrite AGm; [apply DATA; exact Hi|]. apply (outside_hdr V _ V0); rewrite u64 by lia; lia. }
      apply (malloc_part k b V R0 M0 md A); try assumption; try (unfold plen in *; lia).
      refine (regs_ok_pin _ _ _ (21%bv : reg) (EVar 25) HR _). regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite V12, rd8_u, calls_val, V25 by lia.
      unfold calls. rewrite (proj2 (Z.eqb_neq _ _) Hc0). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="L LIBOK limg_intro limg Hplen Htid HCEIL Hvsp"] Theorem body_ok_holds : body_ok sp0 a0s path envv rdraw tid mem0 fs0 data.
  Proof.
    intros k b vals R M md A ST HLc.
    pose proof ST as [_ _ _ _ _ _ _ _ _ _ _ _ BUF _]. pose proof BUF as [_ _ _ _ Hk _ _].
    pose proof (cap_range path data Hplen k Hk) as Hcap. pose proof cfg_range as Hcfg.
    pose proof (dbyte_range data 0) as B0. pose proof (dbyte_range data 1) as B1. pose proof (dbyte_range data 2) as B2.
    unfold t_body.
    replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; unfold L in HLc; lia).
    destruct (Nat.ltb_spec (length data) 6) as [H6|H6].
    { apply (hdr_short sp0 a0s path envv rdraw tid mem0 fs0 data Hvsp HCEIL Htid Hplen k b vals R M md A ST HLc). lia. }
    cbv zeta.
    set (cw := (bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0)))%Z).
    assert (Ecfg : Z.to_nat (cw mod 32768) = Z.to_nat cfg) by (subst cw; unfold cfg, D_Hdqio.cfg, cfgv, dbyte; reflexivity).
    rewrite Ecfg.
    destruct (Nat.ltb_spec (length data) (6 + Z.to_nat cfg)) as [Ho|Ho].
    { apply (hdr_overrun sp0 a0s path envv rdraw tid mem0 fs0 data Hvsp HCEIL Htid Hplen k b vals R M md A ST HLc); [lia|].
      unfold cfg, D_Hdqio.cfg in *. lia. }
    (* [comment removed for export] *)
    pose proof (hdr_run k b vals R M md A ST HLc ltac:(unfold cfg, D_Hdqio.cfg in *; lia)) as RUN.
    unfold succ, calls in RUN.
    destruct (Z.eqb_spec cfg 0) as [Hc0|Hc0].
    - rewrite Hc0. cbn [Z.to_nat] in RUN |- *. exact RUN.
    - destruct (Z.to_nat cfg) as [|c] eqn:Ec; [exfalso; lia|].
      replace (S (Z.to_nat (bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4))) with (Z.to_nat (dbyte data 2 mod 4 + 1)) by (unfold dbyte; pose proof (Z.mod_pos_bound (dbyte data 2) 4 ltac:(lia)); unfold dbyte in *; lia).
      exact RUN.
  Qed.
End Header.
End D_Header.

Module D_Mak2g.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec ShapeAlg Spec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Stmwg D_Manqc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_TrLoop.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Dir LibIface.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Loop OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir.D_Main OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrLoop OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.D_Header OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Dir OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibIface.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.

(* [comment removed for export] *)
Section Top.
  Context {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0}.
  Variable limg : (word -> option byte) -> Prop.
  Hypothesis limg_intro : forall m, Mem.mem_inv RSEGS m ->
    (forall i, (0x30270 <= i < 0x31580)%Z -> m (Z_to_bv 64 i) = None) -> limg m.
  Hypothesis LIBOK : lib_call_ok (LLP limg limg_intro).

  Lemma body_all_holds : body_all.
  Proof.
    intros AMB sp0 a0s path envv rdraw tid regs0 mem0 fs0 fdata Hva Hve Hvsp HCEIL Htid ME Hfile Hplen.
    exact (body_ok_holds sp0 a0s path envv rdraw tid mem0 fs0 fdata Hvsp HCEIL Htid Hplen limg limg_intro LIBOK).
  Qed.

  Theorem ref_realizes_spec_lib :
    forall sp brk mbase rdraw (inp : ProcInput),
      valid_sp sp -> alloc_ceiling = (bv_unsigned sp - 8388608)%Z ->
      valid_brk rsegs brk ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      in_abort_terminal inp = false ->
      realizes rsegs
        (init_config rsegs rpc rph sp brk mbase rdraw D_Mah0u.LIM inp)   (* [comment removed for export] *)
        (spec (in_argv inp) (in_fs inp)).
  Proof. exact (ref_realizes_spec dir_ok_holds body_all_holds). Qed.
End Top.

(* [comment removed for export] *)
Theorem ref_realizes_spec_lib_run {BW : BWorld}
    (AIc : forall Clg : Ceiling, @AllocSpec Clg LayoutP0)
    (DKc : forall Clg : Ceiling, @DriverKit Clg LayoutP0 InitP0 (AIc Clg))
    (limg : (word -> option byte) -> Prop)
    (limg_intro : forall m, Mem.mem_inv RSEGS m ->
       (forall i, (0x30270 <= i < 0x31580)%Z -> m (Z_to_bv 64 i) = None) -> limg m)
    (LIBOK : forall Clg : Ceiling, @lib_call_ok Clg (LLP limg limg_intro) (AIc Clg)) :
  forall sp brk mbase rdraw (inp : ProcInput) (Hsp : valid_sp sp),
    valid_brk rsegs brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    in_abort_terminal inp = false ->
    realizes rsegs
      (init_config rsegs rpc rph sp brk mbase rdraw bw_lim inp)   (* [comment removed for export] *)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rdraw inp Hsp Hbrk Hva Hve Hfit Hab.
  apply (@ref_realizes_spec_lib (ceiling_of_sp (BW:=BW) sp Hsp) (AIc _) (DKc _) limg limg_intro (LIBOK _) sp brk mbase rdraw inp Hsp);
    try assumption.
  unfold alloc_ceiling, ceiling_of_sp. rewrite stack_max_size_val. reflexivity.
Qed.
End D_Mak2g.

From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_T0kc.

Module DU_Hcqt.
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
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Ubsan.
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
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm DU_L06a Spec LibWbxd RefNodes DU_Erh2 DU_Stts DU_Exit RefMocc RefPl89 DU_S6f3 DU_M1ef.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MemSplit D_Kn21w D_Knp98.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Mz0p.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Mz0p.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Abp7.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Wamxh SymAux.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_T8mv.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Tr7g.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Twyu DU_Tr7g.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_L06a OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Erh2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Stts OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Exit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_S6f3 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_M1ef OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Knp98 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mz0p.DU_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mz0p OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tails.DU_Ogma OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Abp7 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tails.DU_Dgah OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Dir.DU_Rcka OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_T8mv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tr7g.DU_TrLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Twyu OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tr7g.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU DriverKit.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.
(* [comment removed for export] *)
Lemma natz_len_range : forall (A : Type) (l : list A) (a b : nat) (za zb : Z),
  Z.of_nat a = za -> Z.of_nat b = zb -> (a <= length l <= b)%nat -> (za <= Z.of_nat (length l) <= zb)%Z.
Proof. intros A l a b za zb <- <- H. split; apply Nat2Z.inj_le; apply H. Qed.
Lemma natz_len_le : forall (A : Type) (l : list A) (b : nat) (zb : Z), Z.of_nat b = zb -> (length l <= b)%nat -> (Z.of_nat (length l) <= zb)%Z.
Proof. intros A l b zb <- H. apply Nat2Z.inj_le; exact H. Qed.
(* [comment removed for export] *)
Lemma natz_len_le_4095 : forall (A : Type) (l : list A), (length l <= 4095)%nat -> (Z.of_nat (length l) <= 4095)%Z.
Proof. intros A l H. exact (natz_len_le A l 4095%nat 4095%Z (@eq_refl Z 4095%Z) H). Qed.
Local Ltac natz_pos_lit p := lazymatch p with xH => idtac | xO ?q => natz_pos_lit q | xI ?q => natz_pos_lit q end.
Local Ltac natz_z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => natz_pos_lit p end.   (* [comment removed for export] *)
Local Ltac natz_kl :=
  repeat match goal with
  | H : (@length ?A ?l <= 4095)%nat |- _ =>
      let Hz := fresh "KLz" in pose proof (natz_len_le_4095 A l H) as Hz; clear H
  | H : (?a <= @length ?A ?l <= ?b)%nat |- _ =>
      let za := eval vm_compute in (Z.of_nat a) in let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit za; natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_range A l a b za zb (@eq_refl Z za) (@eq_refl Z zb) H) as Hz; clear H
  | H : (@length ?A ?l <= ?b)%nat |- _ =>
      let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_le A l b zb (@eq_refl Z zb) H) as Hz; clear H
  end.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Zifyk6b.   (* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= natz_kl; OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Zifyk6b.zon_hook.
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition valsT (vals : list word) (R : bvmap 5 word) (v6 v7 v8 v9 v10 v11 v12 : word) (b L capk owned v calls : Z) : list word :=
  [vals_ev vals 0; vals_ev vals 1; vals_ev vals 2; vals_ev vals 3; vals_ev vals 4; vals_ev vals 5;
   v6; v7; v8; v9; v10; v11; v12;
   getr R 22; getr R 23; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;   (* [comment removed for export] *)
   Z_to_bv 64 b; Z_to_bv 64 L; Z_to_bv 64 capk; Z_to_bv 64 owned; Z_to_bv 64 v; Z_to_bv 64 calls;
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] ++ junk_vals R.

Lemma valsT_length : forall vals R v6 v7 v8 v9 v10 v11 v12 b L capk owned v calls,
  length (valsT vals R v6 v7 v8 v9 v10 v11 v12 b L capk owned v calls) = 70%nat.
Proof. intros. unfold valsT. rewrite length_app, junk_vals_length. reflexivity. Qed.

(* [comment removed for export] *)
Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x123f3) 31 = Some msg_short.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10ce2) 31 = Some msg_overrun.
Proof. vm_compute. reflexivity. Qed.

Lemma resS_eq : stdio_call 70 srS1 knS1 = Some resS. Proof. vm_compute. reflexivity. Qed.
Lemma resV_eq : stdio_call 70 srV1 knV1 = Some resV. Proof. vm_compute. reflexivity. Qed.
Lemma knTL_vars22 : kn_vars_lt 22 knTL = true. Proof. vm_compute. reflexivity. Qed.
Lemma knS2p_incl : kn_incl knTL knS2p = true. Proof. vm_compute. reflexivity. Qed.
Lemma knV2p_incl : kn_incl knTL knV2p = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RS_leaf : list sregion := [(SA (EVar 0) (-8388608), 8388608%Z); (SA (ELit 0) 0x31948, 232%Z)].
Lemma logS1_cov : log_covered RS_leaf (s_log (fst (fst rS1))) = true /\ log_w18 (s_log (fst (fst rS1))) = true.
Proof. vm_compute. split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma logV1_cov : log_covered RS_leaf (s_log (fst (fst rV1))) = true /\ log_w18 (s_log (fst (fst rV1))) = true.
Proof. vm_compute. split; reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Section Leaves.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutPU} {DK : DriverKit LayoutPU InitPU}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variable fs0 : Fs.
  Variable data : list byte.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis Hplen : (length path <= 4095)%nat.

  Let L : Z := Z.of_nat (length data).
  Definition dbyte (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
  Definition cfg : Z := cfgv (dbyte 0) (dbyte 1).

  #[using="L"] Lemma dbyte_range : forall i, (0 <= dbyte i < 256)%Z.
  Proof. clear Hvsp Htid Hfile Hplen. intros i. unfold dbyte. pose proof (bv_unsigned_in_range 8 (nth i data (Z_to_bv 8 0))) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

  Lemma u64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros. apply u_small. assumption. Qed.

  #[using="L Hplen Hvsp data"] Lemma sr_h_ok : forall vals R,
    length vals = 70%nat -> vals_ev vals 0 = sp0 -> junk_at vals R -> pins_main sp0 (p1 sp0 a0s path envv) R ->
    vals_ev vals 2 = p1 sp0 a0s path envv ->
    getr R 9 = vals_ev vals 20 -> getr R 19 = vals_ev vals 21 -> getr R 21 = vals_ev vals 22 ->
    getr R 22 = vals_ev vals 13 -> getr R 23 = vals_ev vals 14 ->
    regs_ok (ENV a0s path rdraw vals) sr_h R.
  Proof.
    intros vals R HL V0 HJ [P2 P3 P4 P8 P18 P20 P24 P25 P26 P27] V2 P9 P19 P21 P22 P23.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_h all_regs];
      try (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
             change (edenot (ENV a0s path rdraw vals) (EVar n)) with (vals_ev vals n);
             first [ let i := eval vm_compute in (n - 38)%nat in
                     etransitivity; [| symmetry; exact (HJ i ltac:(lia))]; f_equal; apply bv_eq; reflexivity
                   | exact P9 | exact P19 | exact P21 | exact P22 | exact P23 | rewrite V2; exact P18 ] end).
    - apply getr_zero.
    - rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. change (vals_ev vals 0) with (vals_ev vals 0). rewrite V0, P2. f_equal; lia.
    - exact P3.
    - exact P4.
    - exact P8.
    - exact P20.
    - exact P24.
    - exact P25.
    - exact P26.
    - exact P27.
  Qed.

  #[using="L Hplen data"] Lemma knH_ok : forall vals M b Lv,
    know_ok RSEGS (ENV a0s path rdraw vals) M knD ->
    vals_ev vals 20 = Z_to_bv 64 b -> (4096 <= b)%Z -> (b <= 0x7fffff800000)%Z ->
    vals_ev vals 21 = Z_to_bv 64 Lv -> (0 <= Lv <= 0x4000000)%Z ->
    know_ok RSEGS (ENV a0s path rdraw vals) M knH.
  Proof.
    intros vals M b Lv HK V20 Hb1 Hb2 V21 HL. unfold knH. apply know_ok_app; [exact HK|].
    constructor; [|constructor; [|constructor]]; apply krange_intro; cbn [edenot ev ENV].
    - rewrite V20, u64 by lia. lia.
    - rewrite V21, u64 by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition VT (vals : list word) (R : bvmap 5 word) (k : nat) (b : Z) (calls : Z) : list word :=
    valsT vals R (rd8 true (dbyte 1)) (rd8 false (dbyte 0)) (rd8 false (dbyte (Z.to_nat cfg + 3))) (rd8 false (dbyte (Z.to_nat cfg + 2)))
          (rd8 false (dbyte (Z.to_nat cfg + 4))) (rd8 false (dbyte (Z.to_nat cfg + 5))) (rd8 false (dbyte 2)) b L (cap k) 0 0 calls.

  #[using="Hplen HCEIL Hvsp"] Lemma hdr_setup : forall k b vals R M md A calls,
    hdr_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A ->
    let V := VT vals R k b calls in
    base_ok sp0 a0s path envv tid V /\ junk_at V R
    /\ regs_ok (ENV a0s path rdraw V) sr_h R /\ know_ok RSEGS (ENV a0s path rdraw V) M knH
    /\ vals_ev V 20 = Z_to_bv 64 b /\ vals_ev V 21 = Z_to_bv 64 L /\ vals_ev V 22 = Z_to_bv 64 (cap k)
    /\ vals_ev V 6 = rd8 true (dbyte 1) /\ vals_ev V 7 = rd8 false (dbyte 0) /\ vals_ev V 12 = rd8 false (dbyte 2)
    /\ vals_ev V 25 = Z_to_bv 64 calls.
  Proof.
    intros k b vals R M md A calls ST V.
    pose proof ST as [HB HJ HP HK HA S1 S3 S5 S6 S7 AI0 MI BUF MD]. (first [ pose proof (HB) as dR_1; dand5 dR_1 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof BUF as [LIVE ONLY DS DATA Hk Hlen HlenL].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_2; dand4 dR_2 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    pose proof (cap_range path data Hplen k Hk) as Hcap.
    assert (HLV : length V = 70%nat) by (subst V; apply valsT_length).
    assert (E0 : vals_ev V 0 = sp0) by (subst V; cbn; exact V0).
    assert (E2 : vals_ev V 2 = p1 sp0 a0s path envv) by (subst V; cbn; exact V2).
    assert (HJV : junk_at V R) by (subst V; unfold valsT; apply junk_at_app; reflexivity).
    assert (E20 : vals_ev V 20 = Z_to_bv 64 b) by reflexivity.
    assert (E21 : vals_ev V 21 = Z_to_bv 64 L) by reflexivity.
    assert (E22 : vals_ev V 22 = Z_to_bv 64 (cap k)) by reflexivity.
    split; [|split; [exact HJV|split; [|split; [|OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity]]]].
    - split; [exact HLV|]. subst V. cbn. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
    - apply (sr_h_ok V R HLV E0 HJV HP E2); rewrite ?E20, ?E21, ?E22; try assumption; subst V; reflexivity.
    - apply (knH_ok V M b L); rewrite ?E20, ?E21; try reflexivity; try lia.
      apply (know_ok_agree RSEGS 6 (ENV a0s path rdraw vals)); [| exact knD_vars | exact HK].
      split; [|reflexivity]. intros i Hi. subst V.
      destruct i as [|[|[|[|[|[|i]]]]]]; [reflexivity .. | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac hdl_index x l i :=
    lazymatch l with
    | x :: _ => i
    | _ :: ?r => hdl_index x r constr:(S i)
    end.
  Ltac hdl_in_tab :=
    lazymatch goal with
    | |- In ?x ?l =>
        let l' := eval red in l in
        let i := hdl_index x l' constr:(O) in
        exact (@nth_error_In _ l i x eq_refl)
    end.
  #[using="Htid mem0 tid sp0"] Lemma know_pieces_S : forall E M, know_ok RSEGS E M knS2 -> know_ok RSEGS E M knS2p.
  Proof.
    intros E M HK. unfold knS2p. change (know_ok RSEGS E M (knS2 ++ kimg_pieces TAIL_PIECES)).
    apply know_ok_app; [exact HK|]. unfold TAIL_PIECES.
    change (kimg_pieces ?l) with
      (kimg_pieces [(0x10000, 0x31948)]%Z ++ (kimg_pieces [(0x31a30, 0x31a38); (0x31b20, 0x31b50)]%Z
       ++ (kimg_pieces [(0x31b51, 0x31b99)]%Z ++ (kimg_pieces [(0x41b99, 0x41ba0); (0x41ba1, 0x41ba4); (0x41ba5, 0x41bd0); (0x41be0, 0x42428)]%Z
       ++ (kimg_pieces [(0x42510, 0x62500)]%Z ++ (kimg_pieces [(0x62538, 0x62548); (0x62668, 0x62768)]%Z
       ++ kimg_pieces [(0x62ba4, 0x62bf8); (0x62ff8, 0x64000)]%Z)))))).
    repeat apply know_ok_app.
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x10000 0x31950); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x319d4 0x31b50); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x31b51 0x31b99); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x41b99 0x42428); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x42510 0x62500); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].   (* [comment removed for export] *)
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x62538 0x62768); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knS2 0x62ba4 0x64000); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
  Qed.

  #[using="Hplen Htid HCEIL Hvsp"] Theorem hdr_short : forall k b vals R M md A,
    hdr_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A -> (L < cap k)%Z -> (L < 6)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17c94) M (seg_rom RSEGS)) md) (t_die msg_short fs0).
  Proof.
    intros k b vals R M md A ST HLc HL6.
    (first [ pose proof ((hdr_setup k b vals R M md A 1 ST)) as dR_3; dand11 dR_3 as HB HJ HR HK V20 V21 V22 V6 V7 V12 V25 | destruct (hdr_setup k b vals R M md A 1 ST) as (HB & HJ & HR & HK & V20 & V21 & V22 & V6 & V7 & V12 & V25) ]).
    set (V := VT vals R k b 1) in *.
    pose proof ST as [HB0 _ HP _ HA S1 S3 S5 S6 S7 AI0 MI BUF MD]. pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof BUF as [LIVE ONLY DS DATA Hk Hlen HlenL].
    (first [ pose proof (HB) as dR_4; dand5 dR_4 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof (cap_range path data Hplen k Hk) as Hcap.
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_5; dand4 dR_5 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    clear HJ HP.
    (* [comment removed for export] *)
    run_block_gen FUEL_X STOPS_X (SCR [true] [] []) 6%nat true.
    { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z; lia. }
    rename EQM into EQM1.
    unfold t_die, W.
    apply (stdio_call_sound_frame V (blobs_ev (blobs0 a0s path rdraw)) srS1 knS1 R0 M0 md resS [] msg_short
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n srS1 knS1) HL) resS_eq));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resS];
      change (Z.of_nat (length msg_short)) with 31%Z; change (Z.of_nat (@length byte [])) with 0%Z.
    - cbn [edenot]. lit_u. lia.
    - cbn [edenot]. lia.
    - cbn [edenot]. lit_u. reflexivity.
    - lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0.
      lit_u. rewrite u_small by lia. lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0.
      lit_u. lit_u. rewrite u_small by lia. lia.
    - cbn [edenot]. lit_u. lit_u. lia.
    - reflexivity.
    - cbn [edenot]. change (length msg_short) with 31%nat.
      rewrite (kimg_rdn RSEGS _ _ knS1 ltac:(let i := kidx knS1 (is_kimg_cov 0x123f3 31) in exact i) _ _ 0x123f3 31 HK eq_refl) by (cbn; lia).
      apply msg_short_img.
    - exact Mfd2.
    - exact Mh.
    - exact Mlz.
    - apply t_exit_has_nil.
    - clear HR HK. intros R1 M1 HR HK SWP.
      change (sc_sr resS) with srS2_0 in HR. change (sc_kn resS) with knS2_0 in HK.
      rewrite ?HL in HR, HK.
      set (vals1 := V ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 102%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (AG1 : forall i, (i < 70)%nat -> vals_ev vals1 i = vals_ev V i) by (intros i Hi; subst vals1; apply vals_ev_app_l; rewrite HL; exact Hi).
      change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path rdraw))) with (ENV a0s path rdraw vals1) in HR, HK.
      (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [] [] []) 102%nat true.
      cbn [mem_denot] in EQM. subst M2.
      (* [comment removed for export] *)
      assert (W1 : ainv A M1 md /\ Mem.mem_inv RSEGS M1).
      { pose proof (mem_denot_frame_mod (ENV a0s path rdraw V) M RS_leaf (s_log (fst (fst rS1))) (proj1 logS1_cov) (proj2 logS1_cov)) as FM.
        assert (RF : regions_flat (ENV a0s path rdraw V) RS_leaf).
        { intros r Hr. unfold RS_leaf in Hr. destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]; rewrite ?V0; try lia.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
        specialize (FM RF).
        replace (mem_denot (ENV a0s path rdraw V) M (s_log (fst (fst rS1)))) with M0 in FM by (rewrite EQM1; reflexivity).
        destruct FM as [AGm Gm].
        destruct SWP as [AGs Gs _ _ _].
        rewrite edenot_add_lit in AGs. unfold adenot, v_addi in AGs. cbn [a_base a_off edenot ev ENV] in AGs. rewrite V0, u64 in AGs by lia.
        apply (drv_client sp0 A M M1 md SPlo ltac:(lia) AI0 MI); [| eapply mem_grows_trans; [exact Gm| exact Gs]].
        intros x N1 N2 N3. rewrite AGs by lia. apply AGm.
        unfold RS_leaf. cbn [map rdenot fst snd outside]. unfold in_rng, estart. cbn [a_base a_off edenot ev ENV]. rewrite V0.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite !u64 by lia. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
      destruct W1 as [AI1 MI1].
      set (valsX := rebase vals1 24 (Z_to_bv 64 2) R2).
      assert (HLX : (NB <= length vals1)%nat) by (rewrite HL1; unfold NB; lia).
      assert (AGX : forall j, (j < NB)%nat -> j <> 24%nat -> vals_ev valsX j = vals_ev V j).
      { intros j Hj Hne. subst valsX. rewrite rebase_lt by (assumption || (unfold NB; lia)). apply AG1. unfold NB in Hj. lia. }
      apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (exit_code 2) (m_fs md)))).
      2:{ rewrite Mfs. apply t_emit_W_nil. apply t_exit_has_nil. }
      apply (tail_exit sp0 a0s path envv rdraw tid Hvsp HCEIL valsX R2 M1 md A b (cap k) 2 (Z_to_bv 64 0x62bf0) (Z_to_bv 64 0) [] false).   (* [comment removed for export] *)
      + split; [apply rebase_length; [exact HLX| unfold NB; lia]|]. rewrite !AGX by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      + apply rebase_junk; [exact HLX| unfold NB; lia].
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite AG1, V0 by lia. f_equal; lia.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + rewrite AGX by (unfold NB; lia). exact V20.
      + subst valsX. apply rebase_at; [exact HLX| unfold NB; lia].
      + lia.
      + regv HR (8%bv : reg). reflexivity.
      + regv HR (9%bv : reg). cbn [edenot ev ENV]. rewrite AG1 by lia. exact V20.
      + apply (know_ok_agree RSEGS 22 (ENV a0s path rdraw vals1)).
        * split; [|reflexivity]. intros i Hi. cbn [ev ENV]. subst valsX. rewrite rebase_lt by (assumption || (unfold NB; lia)). reflexivity.
        * exact knTL_vars22.
        * apply (know_ok_incl RSEGS _ M1 knTL knS2p knS2p_incl). apply know_pieces_S. exact HK.
      + exact AI1.
      + exact LIVE.
      + exact MI1.
      + unfold file_clean. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; krd_solve HK.
      + unfold atexit_st. krd_solve HK.
      + left. split; [reflexivity|]. exists (Z_to_bv 64 0), (Z_to_bv 64 0). unfold file_clean. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; krd_solve HK.
  Qed.
  #[using="Htid mem0 tid sp0"] Lemma know_pieces_V : forall E M, know_ok RSEGS E M knV2 -> know_ok RSEGS E M knV2p.
  Proof.
    intros E M HK. unfold knV2p. change (know_ok RSEGS E M (knV2 ++ kimg_pieces TAIL_PIECES)).
    apply know_ok_app; [exact HK|]. unfold TAIL_PIECES.
    change (kimg_pieces ?l) with
      (kimg_pieces [(0x10000, 0x31948)]%Z ++ (kimg_pieces [(0x31a30, 0x31a38); (0x31b20, 0x31b50)]%Z
       ++ (kimg_pieces [(0x31b51, 0x31b99)]%Z ++ (kimg_pieces [(0x41b99, 0x41ba0); (0x41ba1, 0x41ba4); (0x41ba5, 0x41bd0); (0x41be0, 0x42428)]%Z
       ++ (kimg_pieces [(0x42510, 0x62500)]%Z ++ (kimg_pieces [(0x62538, 0x62548); (0x62668, 0x62768)]%Z
       ++ kimg_pieces [(0x62ba4, 0x62bf8); (0x62ff8, 0x64000)]%Z)))))).
    repeat apply know_ok_app.
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x10000 0x31950); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x319d4 0x31b50); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x31b51 0x31b99); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x41b99 0x42428); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x42510 0x62500); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].   (* [comment removed for export] *)
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x62538 0x62768); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
    - eapply (know_ok_kimg_pieces RSEGS E M knV2 0x62ba4 0x64000); [exact HK| hdl_in_tab| repeat constructor; cbn; lia].
  Qed.

  #[using="Hplen Htid HCEIL Hvsp"] Theorem hdr_overrun : forall k b vals R M md A,
    hdr_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A -> (L < cap k)%Z -> (6 <= L)%Z -> (L < 6 + cfg)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17c94) M (seg_rom RSEGS)) md) (t_die msg_overrun fs0).
  Proof.
    intros k b vals R M md A ST HLc HL6 HLcfg. pose proof (cfgv_range (dbyte 0) (dbyte 1)) as Hcfg. fold cfg in Hcfg.
    pose proof (dbyte_range 0) as B0. pose proof (dbyte_range 1) as B1.
    (first [ pose proof ((hdr_setup k b vals R M md A 1 ST)) as dR_6; dand11 dR_6 as HB HJ HR HK V20 V21 V22 V6 V7 V12 V25 | destruct (hdr_setup k b vals R M md A 1 ST) as (HB & HJ & HR & HK & V20 & V21 & V22 & V6 & V7 & V12 & V25) ]).
    set (V := VT vals R k b 1) in *.
    pose proof ST as [HB0 _ HP _ HA S1 S3 S5 S6 S7 AI0 MI BUF MD]. pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof BUF as [LIVE ONLY DS DATA Hk Hlen HlenL].
    (first [ pose proof (HB) as dR_7; dand5 dR_7 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof (cap_range path data Hplen k Hk) as Hcap.
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_8; dand4 dR_8 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    clear HJ HP.
    (* [comment removed for export] *)
    run_block_gen FUEL_X STOPS_X (SCR [false; true] [] []) 6%nat true.
    { cbn [sc_denot].
      change (branch_taken BC_LTU (vals_ev V 21) (alu64 ALU_ADD (cfgF (vals_ev V 6) (vals_ev V 7)) (Z_to_bv 64 6)) = true).
      rewrite V21, V6, V7, cfgF_val by lia. fold cfg. rewrite alu_add_Z.
      apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_lt. lia. }
    { cbn [sc_denot]. exists [nth 0 data (Z_to_bv 8 0)]. split.
      - unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V20. apply rdn1_of. rewrite u64 by lia. rewrite (DATA 0%Z) by lia. reflexivity.
      - cbn [edenot ev ENV]. rewrite V7. unfold rd8, dbyte. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    { cbn [sc_denot]. exists [nth 1 data (Z_to_bv 8 0)]. split.
      - unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V20. apply rdn1_of. rewrite u64 by lia. rewrite (DATA 1%Z) by lia. reflexivity.
      - cbn [edenot ev ENV]. rewrite V6. unfold rd8, dbyte. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z_false; lia. }
    rename EQM into EQM1.
    unfold t_die, W.
    apply (stdio_call_sound_frame V (blobs_ev (blobs0 a0s path rdraw)) srV1 knV1 R0 M0 md resV [] msg_overrun
             (t_exit (exit_code 2) fs0) HR HK (eq_trans (f_equal (fun n => stdio_call n srV1 knV1) HL) resV_eq));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resV];
      change (Z.of_nat (length msg_overrun)) with 31%Z; change (Z.of_nat (@length byte [])) with 0%Z.
    - cbn [edenot]. lit_u. lia.
    - cbn [edenot]. lia.
    - cbn [edenot]. lit_u. reflexivity.
    - lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0.
      lit_u. rewrite u_small by lia. lia.
    - left. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0.
      lit_u. lit_u. rewrite u_small by lia. lia.
    - cbn [edenot]. lit_u. lit_u. lia.
    - reflexivity.
    - cbn [edenot]. change (length msg_overrun) with 31%nat.
      rewrite (kimg_rdn RSEGS _ _ knV1 ltac:(let i := kidx knV1 (is_kimg_cov 0x10ce2 31) in exact i) _ _ 0x10ce2 31 HK eq_refl) by (cbn; lia).
      apply msg_overrun_img.
    - exact Mfd2.
    - exact Mh.
    - exact Mlz.
    - apply t_exit_has_nil.
    - clear HR HK. intros R1 M1 HR HK SWP.
      change (sc_sr resV) with srV2_0 in HR. change (sc_kn resV) with knV2_0 in HK.
      rewrite ?HL in HR, HK.
      set (vals1 := V ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 102%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (AG1 : forall i, (i < 70)%nat -> vals_ev vals1 i = vals_ev V i) by (intros i Hi; subst vals1; apply vals_ev_app_l; rewrite HL; exact Hi).
      change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path rdraw))) with (ENV a0s path rdraw vals1) in HR, HK.
      (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [] [] []) 102%nat true.
      cbn [mem_denot] in EQM. subst M2.
      (* [comment removed for export] *)
      assert (W1 : ainv A M1 md /\ Mem.mem_inv RSEGS M1).
      { pose proof (mem_denot_frame_mod (ENV a0s path rdraw V) M RS_leaf (s_log (fst (fst rV1))) (proj1 logV1_cov) (proj2 logV1_cov)) as FM.
        assert (RF : regions_flat (ENV a0s path rdraw V) RS_leaf).
        { intros r Hr. unfold RS_leaf in Hr. destruct Hr as [<-|[<-|[]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]; rewrite ?V0; try lia.
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
        specialize (FM RF).
        replace (mem_denot (ENV a0s path rdraw V) M (s_log (fst (fst rV1)))) with M0 in FM by (rewrite EQM1; reflexivity).
        destruct FM as [AGm Gm].
        destruct SWP as [AGs Gs _ _ _].
        rewrite edenot_add_lit in AGs. unfold adenot, v_addi in AGs. cbn [a_base a_off edenot ev ENV] in AGs. rewrite V0, u64 in AGs by lia.
        apply (drv_client sp0 A M M1 md SPlo ltac:(lia) AI0 MI); [| eapply mem_grows_trans; [exact Gm| exact Gs]].
        intros x N1 N2 N3. rewrite AGs by lia. apply AGm.
        unfold RS_leaf. cbn [map rdenot fst snd outside]. unfold in_rng, estart. cbn [a_base a_off edenot ev ENV]. rewrite V0.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite !u64 by lia. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
      destruct W1 as [AI1 MI1].
      set (valsX := rebase vals1 24 (Z_to_bv 64 2) R2).
      assert (HLX : (NB <= length vals1)%nat) by (rewrite HL1; unfold NB; lia).
      assert (AGX : forall j, (j < NB)%nat -> j <> 24%nat -> vals_ev valsX j = vals_ev V j).
      { intros j Hj Hne. subst valsX. rewrite rebase_lt by (assumption || (unfold NB; lia)). apply AG1. unfold NB in Hj. lia. }
      apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (exit_code 2) (m_fs md)))).
      2:{ rewrite Mfs. apply t_emit_W_nil. apply t_exit_has_nil. }
      apply (tail_exit sp0 a0s path envv rdraw tid Hvsp HCEIL valsX R2 M1 md A b (cap k) 2 (Z_to_bv 64 0x62bf0) (Z_to_bv 64 0) [] false).   (* [comment removed for export] *)
      + split; [apply rebase_length; [exact HLX| unfold NB; lia]|]. rewrite !AGX by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      + apply rebase_junk; [exact HLX| unfold NB; lia].
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite AG1, V0 by lia. f_equal; lia.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + rewrite AGX by (unfold NB; lia). exact V20.
      + subst valsX. apply rebase_at; [exact HLX| unfold NB; lia].
      + lia.
      + regv HR (8%bv : reg). reflexivity.
      + regv HR (9%bv : reg). cbn [edenot ev ENV]. rewrite AG1 by lia. exact V20.
      + apply (know_ok_agree RSEGS 22 (ENV a0s path rdraw vals1)).
        * split; [|reflexivity]. intros i Hi. cbn [ev ENV]. subst valsX. rewrite rebase_lt by (assumption || (unfold NB; lia)). reflexivity.
        * exact knTL_vars22.
        * apply (know_ok_incl RSEGS _ M1 knTL knV2p knV2p_incl). apply know_pieces_V. exact HK.
      + exact AI1.
      + exact LIVE.
      + exact MI1.
      + unfold file_clean. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; krd_solve HK.
      + unfold atexit_st. krd_solve HK.
      + left. split; [reflexivity|]. exists (Z_to_bv 64 0), (Z_to_bv 64 0). unfold file_clean. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; krd_solve HK.
  Qed.
End Leaves.
End DU_Hcqt.

Module DU_Hk2b.
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
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Ubsan.
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
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Frame SymExec SymExec2.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm DU_L06a Spec LibWbxd RefNodes DU_Erh2 DU_Stts DU_Exit RefMocc RefPl89 DU_S6f3 DU_M1ef.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require MemSplit D_Kn21w D_Knp98.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Mz0p.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Mz0p.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Abp7.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Tails.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require D_Wamxh SymAux.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_M0r3 DU_Mbtj DU_T8mv.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Tr7g.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Twyu.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Shm0.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Tr7g DU_T0kc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require LibIface.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Frame OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_L06a OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Erh2 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Stts OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Exit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_S6f3 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_M1ef OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Knp98 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mz0p.DU_MainA OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mz0p OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tails.DU_Ogma OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Abp7 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tails.DU_Dgah OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Dir.DU_Rcka OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Dir.DU_Mpqt OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Dir.DU_Loop OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_M0r3 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mbtj OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_T8mv OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tr7g.DU_TrLib OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Twyu OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Shm0.DU_T9tr OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tr7g OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_T0kc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.DU_Hcqt OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibIface.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU DriverKit.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); timeout 8 (Zify.zify; xlia zchecker).   (* timeout-ok: fast tier: hot2_mid's caller catches its failure and runs zify; xlia without it *)
Local Ltac hot_lia_prev := first [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dl_first | tryif OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then first [ hot2_mid | Zify.zify; xlia zchecker ] else first [ solve [OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Zify.zify; xlia zchecker] | hot2_mid | Zify.zify; xlia zchecker ] ].
Local Ltac hot_lia_rest := first [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= first [ solve [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.hplen_pre; hot_lia_rest ] | hot_lia_rest ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac mem_side := cbn; first [ (let E := fresh "E" in intros E; discriminate E) | solve [ OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ exact I | reflexivity ] ] | solve [ repeat first [ left; reflexivity | right ] ] | tauto ].
Local Ltac mem_hyp Hr := cbn in Hr; first [ solve [ repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); first [ discriminate Hr | destruct Hr ] ] | intuition discriminate ].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma knL_vars22b : kn_vars_lt 22 knL = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma knL_knTm : kn_incl knL knTm = true. Proof. vm_compute. reflexivity. Qed.
Lemma knL_knT : kn_incl knL knT = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knT_iw : nat := Eval vm_compute in match kindex (is_kwr_cov (EVar 0) (-8388608) 8388608) knT 0 with Some i => i | None => 0%nat end.
Lemma knT_win : nth_error knT knT_iw = Some (KWr (SA (EVar 0) (-8388608)) 8388608). Proof. vm_compute. reflexivity. Qed.
Lemma knTm_heap_incl : kn_incl knTm (kn_keep2 knTm RS_heap []) = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition kimg_is (lo hi : Z) (e : kentry) : bool := match e with KImg l h => Z.eqb l lo && Z.eqb h hi | _ => false end.
Lemma kimg_in_b : forall lo hi (L : list kentry), existsb (kimg_is lo hi) L = true -> In (KImg lo hi) L.
Proof.
  intros lo hi L H. apply existsb_exists in H as [e [Hin He]]. destruct e; try discriminate He. cbn [kimg_is] in He.
  apply andb_prop in He as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst. exact Hin.
Qed.
(* [comment removed for export] *)
Lemma knT_of_mm : forall E M, know_ok RSEGS E M (kn_afterX rHmm knH) -> know_ok RSEGS E M knT.
Proof.
  intros E M HK. unfold knT. change (know_ok RSEGS E M (knT0 ++ kimg_pieces TR_PIECES)).
  apply know_ok_app; [exact HK|]. unfold TR_PIECES.
  change (kimg_pieces ?l) with
    (kimg_pieces [(0x10000, 0x31a38); (0x10000, 0x31948); (0x31a30, 0x31a38); (0x31b20, 0x31b50)]%Z
     ++ (kimg_pieces [(0x41ba1, 0x41ba4); (0x41ba5, 0x41bd0); (0x41be0, 0x42428)]%Z ++ kimg_pieces [(0x62ba4, 0x62bf8); (0x62ff8, 0x64000)]%Z)).
  repeat apply know_ok_app.
  - eapply (know_ok_kimg_pieces RSEGS E M _ 0x10000 0x31b50); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia].
  - eapply (know_ok_kimg_pieces RSEGS E M _ 0x41ba1 0x42428); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia].
  - eapply (know_ok_kimg_pieces RSEGS E M _ 0x62ba4 0x64000); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia].
Qed.

Ltac knT_of r :=
  intros E M HK;
  apply (know_ok_incl RSEGS E M knT (kn_afterX r knH ++ kimg_pieces TR_PIECES) ltac:(vm_compute; reflexivity));
  apply know_ok_app; [exact HK|]; unfold TR_PIECES;
  change (kimg_pieces ?l) with
    (kimg_pieces [(0x10000, 0x31a38); (0x10000, 0x31948); (0x31a30, 0x31a38); (0x31b20, 0x31b50)]%Z
     ++ (kimg_pieces [(0x41ba1, 0x41ba4); (0x41ba5, 0x41bd0); (0x41be0, 0x42428)]%Z ++ kimg_pieces [(0x62ba4, 0x62bf8); (0x62ff8, 0x64000)]%Z));
  repeat apply know_ok_app;
  [ eapply (know_ok_kimg_pieces RSEGS E M _ 0x10000 0x31b50); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia]
  | eapply (know_ok_kimg_pieces RSEGS E M _ 0x41ba1 0x42428); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia]
  | eapply (know_ok_kimg_pieces RSEGS E M _ 0x62ba4 0x64000); [exact HK| apply kimg_in_b; vm_cast_no_check (@eq_refl bool true)| repeat constructor; cbn; lia] ].

Lemma knT_of_zm : forall E M, know_ok RSEGS E M (kn_afterX rHzm knH) -> know_ok RSEGS E M knT.
Proof. knT_of rHzm. Qed.
Lemma knT_of_mz : forall E M, know_ok RSEGS E M (kn_afterX rHmz knH) -> know_ok RSEGS E M knT.
Proof. knT_of rHmz. Qed.
Lemma knT_of_zz : forall E M, know_ok RSEGS E M (kn_afterX rHzz knH) -> know_ok RSEGS E M knT.
Proof. knT_of rHzz. Qed.

(* [comment removed for export] *)
Definition RS_hdr : list sregion := [(SA (EVar 0) (-8388608), 8388608%Z); (SA (ELit 0) 0x41ba0, 1%Z);
  (SA (ELit 0) 0x62548, 4%Z); (SA (ELit 0) 0x62550, 8%Z); (SA (ELit 0) 0x62560, 8%Z); (SA (ELit 0) 0x62660, 8%Z)].
Lemma logH_cov : forall r, In r [rHmm; rHzm; rHmz; rHzz] ->
  log_covered RS_hdr (s_log (fst (fst r))) = true /\ log_w18 (s_log (fst (fst r))) = true.
Proof. intros r Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; (split; [vm_compute; reflexivity| vm_compute; reflexivity]). Qed.

(* [comment removed for export] *)
Lemma know_knTm_heap : forall E M M',
  know_ok RSEGS E M knTm -> (0x7fff80000000 <= bv_unsigned (ev E 0))%Z ->
  (forall x : word, out_heap (ev E 0) x -> M' x = M x) -> mem_grows M M' -> know_ok RSEGS E M' knTm.
Proof.
  intros E M M' HK Hsp OUT G. apply (know_ok_incl RSEGS E M' knTm _ knTm_heap_incl).
  pose proof (u64_range (ev E 0)) as Hr.
  apply (know_ok_keep2 RSEGS E M M'); [exact HK | | |].
  - unfold RS_heap, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, CSLACK. repeat constructor; unfold estart; cbn [a_base a_off edenot];
      try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  - intros x Hx. apply OUT.
    pose proof (Hx (ELit 0) HEAP_LO (HEAP_HI - HEAP_LO)%Z ltac:(left; reflexivity)) as H1.
    pose proof (Hx (EVar 0) (-8388608 - CSLACK)%Z CSLACK ltac:(right; left; reflexivity)) as H3.
    pose proof (Hx (ELit 0) LOW_LO (LOW_HI - LOW_LO)%Z ltac:(right; right; left; reflexivity)) as H2.
    unfold estart in H1, H2, H3. cbn [a_base a_off edenot] in H1, H2, H3. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in H1, H2.
    unfold CSLACK in H3. unfold out_heap, CSLACK. split; [lia|split; lia].
  - intros x _ Hm. apply G in Hm. exact Hm.
Qed.

Lemma knTm_img : forall E M, know_ok RSEGS E M knTm -> forall i, (0x10000 <= i < 0x31b50)%Z -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M HK i Hi.
  pose proof (know_nth RSEGS _ _ knTm ltac:(let i := kidx knTm (is_kimg_cov 0x31af8 1) in exact i) _ HK eq_refl) as K.
  cbn [kentry_ok] in K. (first [ dand3 K as _ _ K | destruct K as (_ & _ & K) ]). apply K. exact Hi.
Qed.
Lemma knT_img : forall E M, know_ok RSEGS E M knT -> forall i, (0x10000 <= i < 0x31b50)%Z -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M HK i Hi.
  pose proof (know_nth RSEGS _ _ knT ltac:(let i := kidx knT (is_kimg_cov 0x31af8 1) in exact i) _ HK eq_refl) as K.
  cbn [kentry_ok] in K. (first [ dand3 K as _ _ K | destruct K as (_ & _ & K) ]). apply K. exact Hi.
Qed.

Section Header.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutPU} {DK : DriverKit LayoutPU InitPU}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variable fs0 : Fs.
  Variable data : list byte.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hfile : fs_lookup fs0 path = Some data.
  Hypothesis Hplen : (length path <= 4095)%nat.
  (* [comment removed for export] *)
  Variables limg_lo limg_hi : Z.
  Hypothesis Hlimg : (0x10000 <= limg_lo)%Z /\ (limg_hi <= 0x31a38)%Z.
  Variable limg : (word -> option byte) -> Prop.
  Hypothesis limg_intro : forall m, Mem.mem_inv RSEGS m ->
    (forall i, (limg_lo <= i < limg_hi)%Z -> m (Z_to_bv 64 i) = None) -> limg m.
  Hypothesis LIBOK : lib_call_ok (LLU limg_lo limg_hi limg limg_intro).

  Let L : Z := Z.of_nat (length data).
  Definition cfg : Z := DU_Hcqt.cfg data.
  Definition plen : Z := (L - 6 - cfg)%Z.
  Definition cnt : bool := (128 <=? dbyte data 1)%Z.
  Definition calls : Z := (if cfg =? 0 then 1 else dbyte data 2 mod 4 + 1)%Z.
  Definition payload : list byte := skipn (Z.to_nat (6 + cfg)) data.
  Definition v6 : word := rd8 true (dbyte data 1).
  Definition succ : TSet := t_emit (W 1 (zero_lines (Z.to_nat calls))) (t_exit (exit_code 0) fs0).

  Lemma u64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros. apply u_small. assumption. Qed.
  Lemma cfg_range : (0 <= cfg < 32768)%Z. Proof. unfold cfg, DU_Hcqt.cfg. apply cfgv_range. Qed.
  #[using="L Hplen path"] Lemma calls_range : (1 <= calls <= 4)%Z.
  Proof. unfold calls. pose proof (dbyte_range data 2%nat). pose proof (Z.mod_pos_bound (dbyte data 2) 4 ltac:(lia)). destruct (cfg =? 0)%Z; lia. Qed.
  #[using="Hplen path"] Lemma payload_length : (6 + cfg <= L)%Z -> Z.of_nat (length payload) = plen.
  Proof. intros H. unfold payload, plen. rewrite length_skipn. pose proof cfg_range. unfold L in *. lia. Qed.

  (* [comment removed for export] *)
  #[using="LIBOK limg_intro limg Hlimg limg_hi limg_lo Hplen Htid HCEIL Hvsp"] Lemma enter_loop : forall k (j : nat) (b owned aligned : Z) V R M md A,
    (6 + cfg <= L)%Z -> (L < cap k)%Z -> (k <= 10)%nat ->
    ((plen = 0 /\ aligned = 0x41bb0 /\ owned = 0) \/ (0 < plen /\ aligned = owned))%Z ->
    lp_st sp0 a0s path envv rdraw tid fs0 b (cap k) plen owned aligned payload v6 true (S j) 0 V R M md A ->
    (j <= 3)%nat ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17f20) M (seg_rom RSEGS)) md)
             (t_emit (W 1 (zero_lines (S j))) (t_exit (exit_code 0) fs0)).
  Proof.
    intros k j b owned aligned V R M md A HcL HLc Hk Hal ST Hj.
    pose proof (cap_range path data Hplen k Hk) as Hcap. pose proof cfg_range as Hcfg.
    change (zero_lines (S j)) with ([Z_to_bv 8 48; Z_to_bv 8 10] ++ zero_lines j).
    eapply rz_conseq; [| apply t_emit_W_app].
    unfold W at 1. cbn [map].
    apply (tr_entry sp0 a0s path envv rdraw tid Hvsp HCEIL Htid fs0 limg_lo limg_hi Hlimg limg limg_intro LIBOK _ (cap k) plen owned aligned payload v6
             (payload_length HcL) ltac:(unfold plen; lia) Hal j V R M md A _ ST ltac:(lia) (t_emit_has_nil _ _)).
    intros R' M' md' A' ST' INCB'.
    apply (tr_exit sp0 a0s path envv rdraw tid Hvsp HCEIL fs0 _ (cap k) plen owned aligned payload v6 Hal ltac:(unfold plen; lia)
             j V R' M' md' A' (branch_taken BC_LT v6 (Z_to_bv 64 0)) ST' INCB' ltac:(lia) eq_refl).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Vals.
    Variables (V : list word) (b : Z).
    Hypothesis V6 : vals_ev V 6 = rd8 true (dbyte data 1).
    Hypothesis V7 : vals_ev V 7 = rd8 false (dbyte data 0).
    Hypothesis V20 : vals_ev V 20 = Z_to_bv 64 b.
    Hypothesis V21 : vals_ev V 21 = Z_to_bv 64 L.
    Hypothesis Hb : (4096 <= b)%Z /\ (b + 65536 <= 0x7fffff800000)%Z.   (* [comment removed for export] *)
    Hypothesis HL6 : (6 + cfg <= L)%Z /\ (L < 2 ^ 26)%Z.

    #[using="V7 V6 L Hplen"] Lemma cfgX_ev : edenot (ENV a0s path rdraw V) cfgX = Z_to_bv 64 cfg.
    Proof.
      pose proof (dbyte_range data 0). pose proof (dbyte_range data 1).
      unfold ENV. rewrite cfgX_F, V6, V7, cfgF_val by lia. reflexivity.
    Qed.
    #[using="V20 V7 V6 L Hplen"] Lemma baseX_ev : edenot (ENV a0s path rdraw V) (EAlu ALU_ADD (EVar 20) cfgX) = Z_to_bv 64 (b + cfg).
    Proof. change (edenot _ _) with (alu64 ALU_ADD (vals_ev V 20) (edenot (ENV a0s path rdraw V) cfgX)). rewrite V20, cfgX_ev. apply alu_add_Z. Qed.
    #[using="V20 V7 V6 L Hplen"] Lemma payX_ev : edenot (ENV a0s path rdraw V) payX = Z_to_bv 64 (b + cfg + 6).
    Proof. change (edenot _ _) with (alu64 ALU_ADD (edenot (ENV a0s path rdraw V) (EAlu ALU_ADD (EVar 20) cfgX)) (Z_to_bv 64 6)). rewrite baseX_ev. apply alu_add_Z. Qed.
    #[using="HL6 V21 V7 V6 Hplen"] Lemma plenX_ev : edenot (ENV a0s path rdraw V) plenX = Z_to_bv 64 plen.
    Proof.
      pose proof cfg_range.
      change (edenot _ _) with (alu64 ALU_ADD (alu64 ALU_ADD (vals_ev V 21) (mul_div M_MUL (Z_to_bv 64 (-1)) (edenot (ENV a0s path rdraw V) cfgX))) (Z_to_bv 64 (-6))).
      rewrite V21, cfgX_ev. unfold plen. rewrite plen_val by lia. f_equal. lia.
    Qed.
  End Vals.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac ob_rb0 V20 Vn DATA i :=
    cbn [sc_denot]; exists [nth (Z.to_nat i) data (Z_to_bv 8 0)]; split;
    [ unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV]; rewrite V20; apply rdn1_of; rewrite u64 by lia;
      rewrite (DATA i) by lia; reflexivity
    | cbn [edenot ev ENV]; rewrite Vn; unfold rd8, dbyte; rewrite Z_to_bv_bv_unsigned; reflexivity ].
  (* [comment removed for export] *)
  Ltac use_base BASEV :=
    lazymatch type of BASEV with edenot ?E _ = ?v =>
      match goal with |- context [edenot E (EAlu ALU_ADD (EVar 20) ?t)] =>
        replace (edenot E (EAlu ALU_ADD (EVar 20) t)) with v by (symmetry; exact BASEV) end end.
  Ltac ob_rbc b BASEV Vn DATA j :=
    cbn [sc_denot]; exists [nth (Z.to_nat cfg + j) data (Z_to_bv 8 0)]; split;
    [ unfold adenot, v_addi; cbn [a_base a_off]; use_base BASEV; rewrite u64 by lia; apply rdn1_of;
      match goal with |- ?Mx (Z_to_bv 64 ?a) = _ => replace a with (b + (cfg + Z.of_nat j))%Z by lia end;
      rewrite (DATA (cfg + Z.of_nat j)%Z) by lia; do 2 f_equal; lia
    | cbn [edenot ev ENV]; rewrite Vn; unfold rd8, dbyte; rewrite Z_to_bv_bv_unsigned; reflexivity ].
  Ltac ob_flat BASEV :=
    cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; use_base BASEV;
    change (bv_unsigned (edenot _ (ELit 1))) with 1%Z; rewrite u64 by lia; lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac ob_ldisj V20 :=
    solve [ lazymatch goal with |- sc_denot _ _ _ (SCDisj _ _ (SA (ELit 0) _) _) =>
              cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off edenot ev ENV]; rewrite V20;
              change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; change (bv_unsigned (Z_to_bv 64 1)) with 1%Z;
              try change (bv_unsigned (Z_to_bv 64 4)) with 4%Z; try change (bv_unsigned (Z_to_bv 64 8)) with 8%Z;
              rewrite !u64 by lia; OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia end ].
  Ltac ob_sdisj V20 V0 :=
    solve [ lazymatch goal with |- sc_denot _ _ _ (SCDisj _ _ (SA (EVar 0) _) _) =>
              cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off edenot ev ENV]; rewrite V20, V0;
              change (bv_unsigned (Z_to_bv 64 1)) with 1%Z; change (bv_unsigned (Z_to_bv 64 8)) with 8%Z;
              rewrite !u64 by lia; OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia end ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma knTm_eq : kn_keep2 knT (RS_call (-208) MALLOC_STACK) VICT ++ [kwr_data] = knTm.
  Proof. vm_compute. reflexivity. Qed.
  Lemma know_knTm : forall E M', know_ok RSEGS E M' (kn_keep2 knT (RS_call (-208) MALLOC_STACK) VICT) -> know_ok RSEGS E M' knTm.
  Proof. intros E M' HK. rewrite <- knTm_eq. apply know_ok_app; [exact HK | constructor; [apply kwr_data_ok | constructor]]. Qed.
  Lemma payX_vars : expr_vars_lt 70 payX = true. Proof. vm_compute. reflexivity. Qed.
  Lemma plenX_vars : expr_vars_lt 70 plenX = true. Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="L Hplen HCEIL Hvsp data path sp0"] Lemma blk_client : forall A M M' md p n,
    ainv A M md -> a_live A p = Some n -> Mem.mem_inv RSEGS M ->
    (forall x : word, ~ (p <= bv_unsigned x < p + n)%Z -> M' x = M x) -> mem_grows M M' ->
    ainv A M' md /\ Mem.mem_inv RSEGS M'.
  Proof.
    intros A M M' md p n AI0 LV MI OUT G.
    (first [ pose proof ((as_live_ok A M md p n AI0 LV)) as dR_3; dand7 dR_3 as C0 _ P1 HI LO MP NO | destruct (as_live_ok A M md p n AI0 LV) as (C0 & _ & P1 & HI & LO & MP & NO) ]).
    rewrite HCEIL in HI. cbn [al_image_lo al_image_hi LayoutPU] in LO.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0). pose proof alloc_ceiling_val.
    assert (Hh : m_halted md = None) by (destruct (as_lazy_nil A M md AI0) as [_ X]; exact X).
    assert (OUTZ : forall a, (0 <= a < 2 ^ 64)%Z -> ~ (p <= a < p + n)%Z -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N1. apply OUT; rewrite u64 by lia; assumption. }
    split.
    - apply (as_frame A M M' md md AI0).
      + intros a Ho. pose proof (owned_azone A M md a AI0 Ho) as ZZ. unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in ZZ.
        apply OUTZ; [lia|]. intros Hin. apply (NO (a - p)%Z ltac:(lia)). replace (p + (a - p))%Z with a by lia. exact Ho.
      + intros a Hs. cbn [al_shared LayoutPU] in Hs. unfold pu_shared in Hs. apply OUTZ; lia.
      + intros q c i HL Hi. (first [ pose proof ((as_live_ok A M md q c AI0 HL)) as dR_4; dand7 dR_4 as _ _ _ _ _ MPq _ | destruct (as_live_ok A M md q c AI0 HL) as (_ & _ & _ & _ & _ & MPq & _) ]). apply G. apply MPq. exact Hi.
      + intros a [Ha Hni] Hm. rewrite HCEIL in Ha. unfold in_image in Hni. cbn [al_image_lo al_image_hi LayoutPU] in Hni.
        destruct (Z_lt_le_dec a p) as [L1|L1]; [rewrite OUTZ in Hm by lia; exact Hm|].
        destruct (Z_lt_le_dec a (p + n)) as [L2|L2]; [|rewrite OUTZ in Hm by lia; exact Hm].
        replace a with (p + (a - p))%Z by lia. apply MP. lia.
      + reflexivity.
      + exact Hh.
    - intros x v Hx. destruct (Mem.ro_addr RSEGS x) eqn:RO; [|reflexivity]. exfalso.
      pose proof (proj1 (as_ro_addr_iff (AI:=AI) x) RO) as RA. cbn [al_image_lo al_rw_lo LayoutPU] in RA.
      rewrite OUT in Hx by lia. pose proof (MI x v Hx) as RO'. rewrite RO' in RO. discriminate.
  Qed.

  #[using="LIBOK limg_intro limg Hlimg limg_hi limg_lo Hplen Htid HCEIL Hvsp mem0"] Lemma malloc_part : forall k b V R M md A,
    regs_ok (ENV a0s path rdraw V) sr_m R ->
    know_ok RSEGS (ENV a0s path rdraw V) M knT ->
    base_ok sp0 a0s path envv tid V ->
    vals_ev V 6 = rd8 true (dbyte data 1) -> vals_ev V 7 = rd8 false (dbyte data 0) ->
    vals_ev V 20 = Z_to_bv 64 b -> vals_ev V 21 = Z_to_bv 64 L -> vals_ev V 25 = Z_to_bv 64 calls ->
    ainv A M md -> Mem.mem_inv RSEGS M -> MDcl fs0 md ->
    a_live A b = Some (cap k) -> (a_livebytes A = cap k /\ a_nlive A = 1%Z) ->   (* [comment removed for export] *)
    (forall i, (0 <= i < L)%Z -> M (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))) ->
    (k <= 10)%nat -> (L < cap k)%Z -> (6 + cfg <= L)%Z -> (0 < plen)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x23364) M (seg_rom RSEGS)) md) succ.   (* [comment removed for export] *)
  Proof.
    intros k b V R M md A HR HK HB V6 V7 V20 V21 V25 AI0 MI MD LIVE DS DATA Hk HLc HcL Hp.
    (first [ pose proof (HB) as dR_5; dand5 dR_5 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]). pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof (cap_range path data Hplen k Hk) as Hcap. pose proof cfg_range as Hcfg. pose proof calls_range as Hcalls.
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_6; dand4 dR_6 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    pose proof (dbyte_range data 0) as B0. pose proof (dbyte_range data 1) as B1. pose proof (dbyte_range data 2) as B2.
    assert (HLV : (6 + cfg <= L)%Z /\ (L < 2 ^ 26)%Z) by lia.
    pose proof (plenX_ev V V6 V7 V21 HLV) as PLENV. pose proof (payX_ev V b V6 V7 V20) as PAYV.
    assert (Hpl : (0 < plen < 2 ^ 26)%Z) by (unfold plen in *; lia).
    assert (CH : callH V (blobs_ev (blobs0 a0s path rdraw)) sr_m knT plen (-208) 0x17ecc).
    { split; rewrite ?HL, ?V0; try reflexivity; try lia.
      - exact PLENV.
      - exists knT_iw. exact knT_win. }
    destruct DS as [LB0 NL0].
    apply (W_malloc_nf V (blobs_ev (blobs0 a0s path rdraw)) sr_m knT R M md A plen (-208) 0x17ecc _ HR HK CH AI0
             (ex_intro _ b (ex_intro _ (cap k) LIVE)) MI ltac:(lia) ltac:(rewrite NREQ_CAP_eq; lia)
             ltac:(rewrite LIVE_MAX_eq, LB0; lia) ltac:(rewrite NLIVE_MAX_eq, NL0; lia)).
    (* [comment removed for export] *)
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 md1 A1 r Hr Hv80 HR HK1 AI1 MI1 MF1 NONE1 LIVE1 OTHER1 LB1 NL1 FR1.
      pose proof (know_knTm _ M1 HK1) as HK. clear HK1.
      assert (Hh1 : m_halted md1 = None) by (destruct (as_lazy_nil A1 M1 md1 AI1) as [_ X]; exact X).
      assert (Hl1 : m_vm_lazy md1 = []) by (destruct (as_lazy_nil A1 M1 md1 AI1) as [X _]; exact X).
      rewrite HL in HR, Hv80. change (sr_post sr_m 70) with srB_0 in HR. change (70 + 10)%nat with 80%nat in Hv80.
      set (vals1 := V ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 102%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (AG1 : forall i, (i < 70)%nat -> vals_ev vals1 i = vals_ev V i) by (intros i Hi; subst vals1; apply vals_ev_app_l; rewrite HL; exact Hi).
      change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path rdraw))) with (ENV a0s path rdraw vals1) in HR, HK.
      (first [ pose proof ((block_range sp0 path data HCEIL Hplen A1 M1 md1 r plen AI1 LIVE1)) as dR_8; dand4 dR_8 as _ Hr16 HrLO HrHI | destruct (block_range sp0 path data HCEIL Hplen A1 M1 md1 r plen AI1 LIVE1) as (_ & Hr16 & HrLO & HrHI) ]). unfold HEAP_LO, LOW_HI in HrLO.
      assert (Hrb : r <> b) by (intros ->; rewrite LIVE in NONE1; discriminate).
      assert (LIVEB1 : a_live A1 b = Some (cap k)) by (rewrite (OTHER1 b ltac:(congruence)); exact LIVE).
      pose proof (as_live_disjoint A1 M1 md1 b (cap k) r plen AI1 LIVEB1 LIVE1 ltac:(congruence)) as DISJ.
      rewrite V0 in FR1.
      assert (DATA1 : forall i, (0 <= i < L)%Z -> M1 (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. rewrite <- (DATA i Hi).
        apply (block_acall sp0 path data Hvsp HCEIL Hplen A A1 M M1 md md1 (-208) MALLOC_STACK nowhere (blk r plen) b (cap k) AI0 AI1 LIVE FR1);
          [unfold MALLOC_STACK; lia | intros j Hj Hv; exact Hv | | lia].
        intros j Hj [_ Hin]. lia. }
      (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [false] [] []) 102%nat true.
      { cbn [sc_denot edenot ev ENV]. rewrite Hv80, bt_eq0_Z by lia. apply Z.eqb_neq. lia. }
      cbn [mem_denot] in EQM. subst M0.
      assert (PAYL : length payload = Z.to_nat plen) by (pose proof (payload_length HcL); lia).
      assert (MCH : mcH M1 (Z_to_bv 64 r) (Z_to_bv 64 (b + cfg + 6)) plen payload).
      { split.
        - lia.
        - exact PAYL.
        - apply rdn_pointwise; [reflexivity | rewrite u64, PAYL by lia; unfold plen in *; lia |].
          intros j Hj. rewrite u64 by lia. rewrite PAYL in Hj.
          replace (b + cfg + 6 + Z.of_nat j)%Z with (b + (6 + cfg + Z.of_nat j))%Z by lia.
          rewrite (DATA1 (6 + cfg + Z.of_nat j)%Z) by (unfold plen in *; lia).
          unfold payload. rewrite nth_skipn. do 2 f_equal. lia.
        - rewrite PAYL. eapply (block_store_ok sp0 path data Hvsp HCEIL Hplen A1 M1 md1 r plen); [exact AI1| exact LIVE1| lia| lia].
        - rewrite !u64 by lia. unfold plen in *. lia.
        - rewrite u64 by lia. unfold plen in *. lia.
        - rewrite u64 by lia. lia. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?RR _ _ _) _) _ => rename RR into R2 end.
      destruct (ref_memcpy M1 (Z_to_bv 64 r) (Z_to_bv 64 (b + cfg + 6)) plen payload (seg_rom RSEGS) MCH R2 (Z_to_bv 64 0x17ee0))
        as [R3 [MS KEEPS]].
      { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
      { regv HR (1%bv : reg). reflexivity. }
      { regv HR (10%bv : reg). cbn [edenot ev ENV]. exact Hv80. }
      { regv HR (11%bv : reg). subst vals1. exact (eq_trans (env_app_edenot V (junk_vals R1) (blobs_ev (blobs0 a0s path rdraw)) payX ltac:(rewrite HL; exact payX_vars)) PAYV). }
      { regv HR (12%bv : reg). subst vals1. exact (eq_trans (env_app_edenot V (junk_vals R1) (blobs_ev (blobs0 a0s path rdraw)) plenX ltac:(rewrite HL; exact plenX_vars)) PLENV). }
      replace (Z_to_bv 64 0x2aff4) with (0x2aff4 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh1 | exact Hl1 | exact MS |].
      set (M3 := wbytes M1 (Z_to_bv 64 r) payload) in *.
      assert (OUT3 : forall x : word, ~ (r <= bv_unsigned x < r + plen)%Z -> M3 x = M1 x).
      { intros x Hx. subst M3. apply wbytes_outside; rewrite u64, ?PAYL by lia; unfold in_rng; rewrite ?u64 by lia; lia. }
      assert (IN3 : forall i, (0 <= i < plen)%Z -> M3 (Z_to_bv 64 (r + i)) = Some (nth (Z.to_nat i) payload (Z_to_bv 8 0))).
      { intros i Hi. subst M3. rewrite wbytes_inside by (rewrite ?PAYL, !u64 by lia; lia). rewrite !u64 by lia.
        replace (Z.to_nat (r + i - r)) with (Z.to_nat i) by lia. reflexivity. }
      assert (G3 : mem_grows M1 M3) by (subst M3; apply wbytes_grows).
      assert (HK3 : know_ok RSEGS (ENV a0s path rdraw vals1) M3 knTm).
      { apply (know_knTm_heap _ M1 M3 HK); [cbn [ev ENV]; rewrite ?AG2, ?AG1 by lia; rewrite V0; lia | | exact G3].
        intros x [Hx1 [Hx2 Hx3]]. cbn [ev ENV] in Hx2. rewrite ?AG2, ?AG1 in Hx2 by lia. rewrite V0 in Hx2. apply OUT3. unfold HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, CSLACK in Hx1, Hx2, Hx3. lia. }
      destruct (blk_client A1 M1 M3 md1 r plen AI1 LIVE1 MI1 OUT3 G3) as [AI3 MI3].
      (* [comment removed for export] *)
      destruct (tr_c R3 M3 (seg_rom RSEGS)) as (R4 & MS4 & S9 & S22 & S23 & KEEP4).
      replace (Z_to_bv 64 0x17ee0) with (0x17ee0 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh1 | exact Hl1 | exact MS4 |].
      replace (0x17f20 : word) with (Z_to_bv 64 0x17f20) by (apply bv_eq; reflexivity).
      assert (KR : forall rr : reg, In rr callee_kept -> rr <> 9%bv -> rr <> 22%bv -> rr <> 23%bv -> getr R4 rr = getr R2 rr).
      { intros rr Hin H9 H22 H23. rewrite KEEP4 by assumption. apply KEEPS. exact Hin. }
      set (j := (Z.to_nat calls - 1)%nat).
      replace succ with (t_emit (W 1 (zero_lines (S j))) (t_exit (exit_code 0) fs0)) by (unfold succ; f_equal; f_equal; f_equal; subst j; lia).
      set (valsL := rebase vals1 23 (Z_to_bv 64 r) R4).
      assert (HLX : (NB <= length vals1)%nat) by (rewrite HL1; unfold NB; lia).
      assert (AGX : forall q, (q < NB)%nat -> q <> 23%nat -> vals_ev valsL q = vals_ev V q).
      { intros q Hq Hne. subst valsL. rewrite rebase_lt by (assumption || (unfold NB; lia)). apply AG1. unfold NB in Hq. lia. }
      apply (enter_loop k j b r r valsL R4 M3 md1 A1 HcL HLc Hk ltac:(right; lia)); [| subst j; lia].
      split.
      + split; [apply rebase_length; [exact HLX| unfold NB; lia]|]. rewrite !AGX by (unfold NB; lia). OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      + rewrite AGX by (unfold NB; lia). exact V6.
      + rewrite AGX by (unfold NB; lia). exact V20.
      + subst valsL. apply rebase_at; [exact HLX| unfold NB; lia].
      + apply (know_ok_agree RSEGS 22 (ENV a0s path rdraw vals1)).
        * split; [|reflexivity]. intros i Hi. cbn [ev ENV]. subst valsL. rewrite rebase_lt by (assumption || (unfold NB; lia)). reflexivity.
        * exact knL_vars22b.
        * apply (know_ok_incl RSEGS _ M3 knL knTm knL_knTm). exact HK3.
      + rewrite KR by mem_side. regv HR (2%bv : reg).
        rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite AG1, V0 by lia. f_equal; lia.
      + rewrite KR by mem_side. regv HR (3%bv : reg). reflexivity.
      + rewrite KR by mem_side. regv HR (4%bv : reg). reflexivity.
      + rewrite KR by mem_side. regv HR (8%bv : reg).
        subst vals1. exact (eq_trans (env_app_edenot V (junk_vals R1) (blobs_ev (blobs0 a0s path rdraw)) plenX ltac:(rewrite HL; exact plenX_vars)) PLENV).
      + rewrite S9. rewrite (KEEPS 18%bv ltac:(mem_side)). regv HR (18%bv : reg). cbn [edenot ev ENV]. exact Hv80.
      + rewrite KR by mem_side. regv HR (18%bv : reg). cbn [edenot ev ENV]. exact Hv80.
      + rewrite KR by mem_side. regv HR (20%bv : reg). reflexivity.
      + rewrite KR by mem_side. regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite AG1 by lia. rewrite V25.
        f_equal. subst j. lia.
      + exact S22.
      + exact S23.
      + exact AI3.
      + exact MI3.
      + (first [ dand4 MF1 as FD _ FS _ | destruct MF1 as (FD & _ & FS & _) ]). split.
        * unfold m_fs. rewrite FS. exact Mfs.
        * unfold m_fds. rewrite FD. exact Mfd1.
        * unfold m_fds. rewrite FD. exact Mfd2.
        * exact Hh1.
        * exact Hl1.
      + exact LIVEB1.
      + right. split; [exact LIVE1| exact IN3].
      + intros i Hi. rewrite OUT3 by (rewrite u64 by lia; lia). apply (knTm_img _ M1 HK). lia.
      + (* [comment removed for export] *)
        rewrite LB1, NL1, LB0, NL0, LIVE_MAX_eq, NLIVE_MAX_eq. unfold LIB_LIVE, LIB_NLIVE. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac hdr_frame r V M M0 EQM V0 AGm Gm :=
    let FM := fresh "FM" in let RF := fresh "RF" in
    pose proof (mem_denot_frame_mod (ENV a0s path rdraw V) M RS_hdr (s_log (fst (fst r)))
                  (proj1 (logH_cov r ltac:(mem_side))) (proj2 (logH_cov r ltac:(mem_side)))) as FM;
    assert (RF : regions_flat (ENV a0s path rdraw V) RS_hdr)
      by (intros rr Hr; unfold RS_hdr in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]; rewrite ?V0;
          first [lia | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia]);
    specialize (FM RF);
    replace (mem_denot (ENV a0s path rdraw V) M (s_log (fst (fst r)))) with M0 in FM by (rewrite EQM; reflexivity);
    destruct FM as [AGm Gm]; clear RF.

  (* [comment removed for export] *)
  #[using="L Hplen Hvsp data"] Lemma outside_hdr : forall V (x : word),
    vals_ev V 0 = sp0 ->
    ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z -> ~ (0x41ba0 <= bv_unsigned x < 0x62668)%Z ->
    outside x (map (rdenot (ENV a0s path rdraw V)) RS_hdr).
  Proof.
    intros V x V0 N1 N2. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    unfold RS_hdr. cbn [map rdenot fst snd outside]. unfold in_rng, estart. cbn [a_base a_off edenot ev ENV]. rewrite V0.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite !u64 by lia. OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.

  #[using="LIBOK limg_intro limg Hlimg limg_hi limg_lo Hplen Htid HCEIL Hvsp"] Theorem hdr_run : forall k b vals R M md A,
    hdr_st sp0 a0s path envv rdraw tid mem0 fs0 data k b vals R M md A -> (L < cap k)%Z -> (6 + cfg <= L)%Z ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17c94) M (seg_rom RSEGS)) md) succ.   (* [comment removed for export] *)
  Proof.
    intros k b vals R M md A ST HLc HcL.
    (first [ pose proof ((hdr_setup sp0 a0s path envv rdraw tid mem0 fs0 data Hvsp HCEIL Hplen k b vals R M md A calls ST)) as dR_11; dand11 dR_11 as HB HJ HR HK V20 V21 V22 V6 V7 V12 V25 | destruct (hdr_setup sp0 a0s path envv rdraw tid mem0 fs0 data Hvsp HCEIL Hplen k b vals R M md A calls ST)
      as (HB & HJ & HR & HK & V20 & V21 & V22 & V6 & V7 & V12 & V25) ]).
    set (V := VT data vals R k b calls) in *.
    pose proof ST as [HB0 _ HP _ HA S1 S3 S5 S6 S7 AI0 MI BUF MD]. pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof BUF as [LIVE ONLY DS DATA Hk Hlen HlenL].
    (first [ pose proof (HB) as dR_12; dand5 dR_12 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof (cap_range path data Hplen k Hk) as Hcap. pose proof cfg_range as Hcfg. pose proof calls_range as Hcalls.
    (first [ pose proof ((block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE)) as dR_13; dand4 dR_13 as _ Hb16 HbLO HbHI | destruct (block_range sp0 path data HCEIL Hplen A M md b (cap k) AI0 LIVE) as (_ & Hb16 & HbLO & HbHI) ]). unfold HEAP_LO, LOW_HI in HbLO.
    pose proof (dbyte_range data 0) as B0. pose proof (dbyte_range data 1) as B1. pose proof (dbyte_range data 2) as B2.
    assert (HbV : (4096 <= b)%Z /\ (b + 65536 <= 0x7fffff800000)%Z) by lia.
    assert (HLV : (6 + cfg <= L)%Z /\ (L < 2 ^ 26)%Z) by lia.
    pose proof (baseX_ev V b V6 V7 V20) as BASEV. pose proof (plenX_ev V V6 V7 V21 HLV) as PLENV. pose proof (cfgX_ev V V6 V7) as CFGV.
    assert (V8 : vals_ev V 8 = rd8 false (dbyte data (Z.to_nat cfg + 3))) by reflexivity.
    assert (V9 : vals_ev V 9 = rd8 false (dbyte data (Z.to_nat cfg + 2))) by reflexivity.
    assert (V10 : vals_ev V 10 = rd8 false (dbyte data (Z.to_nat cfg + 4))) by reflexivity.
    assert (V11 : vals_ev V 11 = rd8 false (dbyte data (Z.to_nat cfg + 5))) by reflexivity.
    clear HJ HP.
    destruct (Z.eqb_spec cfg 0) as [Hc0|Hc0]; destruct (Z.eqb_spec plen 0) as [Hp0|Hp0].
    - (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [false; false; true; false] [] []) 6%nat true.
      all: try (ob_sdisj V20 V0).
      { cbn [sc_denot]. change (branch_taken BC_NE (edenot (ENV a0s path rdraw V) plenX) (Z_to_bv 64 0) = false). rewrite PLENV, bt_ne0_Z by (unfold plen; lia). rewrite (proj2 (Z.eqb_eq _ _) Hp0). reflexivity. }
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 0) = true). rewrite CFGV, bt_eq0_Z by lia. rewrite (proj2 (Z.eqb_eq _ _) Hc0). reflexivity. }
      { ob_rbc b BASEV V11 DATA 5%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V10 DATA 4%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V9 DATA 2%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V8 DATA 3%nat. }
      { ob_flat BASEV. }
      { cbn [sc_denot]. change (branch_taken BC_LTU (vals_ev V 21) (alu64 ALU_ADD (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 6)) = false).
        rewrite V21, CFGV, alu_add_Z. apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_ge. lia. }
      { ob_rb0 V20 V7 DATA 0%Z. }
      { ob_rb0 V20 V6 DATA 1%Z. }
      { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z_false; lia. }
      (* [comment removed for export] *)
      pose proof (knT_of_zz _ M0 HK) as HKT.
      hdr_frame rHzz V M M0 EQM V0 AGm Gm.
      assert (W0 : ainv A M0 md /\ Mem.mem_inv RSEGS M0).
      { apply (drv_client sp0 A M M0 md SPlo ltac:(lia) AI0 MI); [| exact Gm]. intros x N1 N2 N3. apply AGm. apply (outside_hdr V x V0); lia. }
      destruct W0 as [AI0' MI0'].
      cbv beta iota.
      replace succ with (t_emit (W 1 (zero_lines 1)) (t_exit (exit_code 0) fs0))
        by (unfold succ, calls; rewrite (proj2 (Z.eqb_eq _ _) Hc0); reflexivity).
      apply (enter_loop k 0 b 0 0x41bb0 V R0 M0 md A HcL HLc Hk ltac:(left; lia)); [| lia].
      split.
      + exact HB. + exact V6. + exact V20. + reflexivity.
      + apply (know_ok_incl RSEGS _ M0 knL knT knL_knT). exact HKT.
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0. f_equal; lia.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + regv HR (8%bv : reg). exact PLENV.
      + regv HR (9%bv : reg). reflexivity.
      + regv HR (18%bv : reg). reflexivity.
      + regv HR (20%bv : reg). reflexivity.
      + regv HR (21%bv : reg). reflexivity.
      + regv HR (22%bv : reg). reflexivity.
      + regv HR (23%bv : reg). reflexivity.
      + exact AI0'.
      + exact MI0'.
      + split; assumption.
      + exact LIVE.
      + left. exact Hp0.
      + intros i Hi. apply (knT_img _ M0 HKT). lia.
      + (* [comment removed for export] *)
        destruct DS as [LB0 NL0]. rewrite LB0, NL0, Hp0, LIVE_MAX_eq, NLIVE_MAX_eq. unfold LIB_LIVE, LIB_NLIVE. lia.
    - (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [false; false; true; true] [] []) 6%nat true.
      all: try (ob_sdisj V20 V0).
      { cbn [sc_denot]. change (branch_taken BC_NE (edenot (ENV a0s path rdraw V) plenX) (Z_to_bv 64 0) = true). rewrite PLENV, bt_ne0_Z by (unfold plen; lia).
        rewrite (proj2 (Z.eqb_neq _ _) Hp0). reflexivity. }
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 0) = true). rewrite CFGV, bt_eq0_Z by lia. rewrite (proj2 (Z.eqb_eq _ _) Hc0). reflexivity. }
      { ob_rbc b BASEV V11 DATA 5%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V10 DATA 4%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V9 DATA 2%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V8 DATA 3%nat. }
      { ob_flat BASEV. }
      { cbn [sc_denot]. change (branch_taken BC_LTU (vals_ev V 21) (alu64 ALU_ADD (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 6)) = false).
        rewrite V21, CFGV, alu_add_Z. apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_ge. lia. }
      { ob_rb0 V20 V7 DATA 0%Z. }
      { ob_rb0 V20 V6 DATA 1%Z. }
      { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z_false; lia. }
      cbv beta iota.
      pose proof (knT_of_zm _ M0 HK) as HKT.
      hdr_frame rHzm V M M0 EQM V0 AGm Gm.
      assert (W0 : ainv A M0 md /\ Mem.mem_inv RSEGS M0).
      { apply (drv_client sp0 A M M0 md SPlo ltac:(lia) AI0 MI); [| exact Gm]. intros x N1 N2 N3. apply AGm. apply (outside_hdr V x V0); lia. }
      destruct W0 as [AI0' MI0'].
      assert (DATA0 : forall i, (0 <= i < L)%Z -> M0 (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. rewrite AGm; [apply DATA; exact Hi|]. apply (outside_hdr V _ V0); rewrite u64 by lia; lia. }
      apply (malloc_part k b V R0 M0 md A); try assumption; try (unfold plen in *; lia).
      refine (regs_ok_pin _ _ _ (21%bv : reg) (EVar 25) HR _). regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite V25. unfold calls. rewrite (proj2 (Z.eqb_eq _ _) Hc0). reflexivity.
    - (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [false; false; false; true] [] []) 6%nat true.
      all: try (ob_sdisj V20 V0). all: try (ob_ldisj V20).
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) plenX) (Z_to_bv 64 0) = true). rewrite PLENV, bt_eq0_Z by (unfold plen; lia).
        rewrite (proj2 (Z.eqb_eq _ _) Hp0). reflexivity. }
      { ob_rb0 V20 V12 DATA 2%Z. }
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 0) = false). rewrite CFGV, bt_eq0_Z by lia. rewrite (proj2 (Z.eqb_neq _ _) Hc0). reflexivity. }
      { ob_rbc b BASEV V11 DATA 5%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V10 DATA 4%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V9 DATA 2%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V8 DATA 3%nat. }
      { ob_flat BASEV. }
      { cbn [sc_denot]. change (branch_taken BC_LTU (vals_ev V 21) (alu64 ALU_ADD (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 6)) = false).
        rewrite V21, CFGV, alu_add_Z. apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_ge. lia. }
      { ob_rb0 V20 V7 DATA 0%Z. }
      { ob_rb0 V20 V6 DATA 1%Z. }
      { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z_false; lia. }
      pose proof (knT_of_mz _ M0 HK) as HKT.
      hdr_frame rHmz V M M0 EQM V0 AGm Gm.
      assert (W0 : ainv A M0 md /\ Mem.mem_inv RSEGS M0).
      { apply (drv_client sp0 A M M0 md SPlo ltac:(lia) AI0 MI); [| exact Gm]. intros x N1 N2 N3. apply AGm. apply (outside_hdr V x V0); lia. }
      destruct W0 as [AI0' MI0'].
      cbv beta iota.
      set (j := Z.to_nat (dbyte data 2 mod 4)).
      pose proof (Z.mod_pos_bound (dbyte data 2) 4 ltac:(lia)) as Hm4.
      replace succ with (t_emit (W 1 (zero_lines (S j))) (t_exit (exit_code 0) fs0)).
      2:{ unfold succ, calls. rewrite (proj2 (Z.eqb_neq _ _) Hc0). f_equal. f_equal. f_equal. subst j. lia. }
      apply (enter_loop k j b 0 0x41bb0 V R0 M0 md A HcL HLc Hk ltac:(left; lia)); [| subst j; lia].
      split.
      + exact HB. + exact V6. + exact V20. + reflexivity.
      + apply (know_ok_incl RSEGS _ M0 knL knT knL_knT). exact HKT.
      + regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite V0. f_equal; lia.
      + regv HR (3%bv : reg). reflexivity.
      + regv HR (4%bv : reg). reflexivity.
      + regv HR (8%bv : reg). exact PLENV.
      + regv HR (9%bv : reg). reflexivity.
      + regv HR (18%bv : reg). reflexivity.
      + regv HR (20%bv : reg). reflexivity.
      + regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite V12, rd8_u by lia. rewrite calls_val by lia. f_equal. subst j. lia.
      + regv HR (22%bv : reg). reflexivity.
      + regv HR (23%bv : reg). reflexivity.
      + exact AI0'.
      + exact MI0'.
      + split; assumption.
      + exact LIVE.
      + left. exact Hp0.
      + intros i Hi. apply (knT_img _ M0 HKT). lia.
      + (* [comment removed for export] *)
        destruct DS as [LB0 NL0]. rewrite LB0, NL0, Hp0, LIVE_MAX_eq, NLIVE_MAX_eq. unfold LIB_LIVE, LIB_NLIVE. lia.
    - (* [comment removed for export] *)
      run_block_gen FUEL_X STOPS_X (SCR [false; false; false; false] [] []) 6%nat true.
      all: try (ob_sdisj V20 V0). all: try (ob_ldisj V20).
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) plenX) (Z_to_bv 64 0) = false). rewrite PLENV, bt_eq0_Z by (unfold plen; lia).
        rewrite (proj2 (Z.eqb_neq _ _) Hp0). reflexivity. }
      { ob_rb0 V20 V12 DATA 2%Z. }
      { cbn [sc_denot]. change (branch_taken BC_EQ (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 0) = false). rewrite CFGV, bt_eq0_Z by lia. rewrite (proj2 (Z.eqb_neq _ _) Hc0). reflexivity. }
      { ob_rbc b BASEV V11 DATA 5%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V10 DATA 4%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V9 DATA 2%nat. }
      { ob_flat BASEV. }
      { ob_rbc b BASEV V8 DATA 3%nat. }
      { ob_flat BASEV. }
      { cbn [sc_denot]. change (branch_taken BC_LTU (vals_ev V 21) (alu64 ALU_ADD (edenot (ENV a0s path rdraw V) cfgX) (Z_to_bv 64 6)) = false).
        rewrite V21, CFGV, alu_add_Z. apply bt_ltu_Z; [lia| lia|]. apply Z.ltb_ge. lia. }
      { ob_rb0 V20 V7 DATA 0%Z. }
      { ob_rb0 V20 V6 DATA 1%Z. }
      { cbn [sc_denot edenot ev ENV]. rewrite V21. apply bt_geu_Z_false; lia. }
      cbv beta iota.
      pose proof (knT_of_mm _ M0 HK) as HKT.
      hdr_frame rHmm V M M0 EQM V0 AGm Gm.
      assert (W0 : ainv A M0 md /\ Mem.mem_inv RSEGS M0).
      { apply (drv_client sp0 A M M0 md SPlo ltac:(lia) AI0 MI); [| exact Gm]. intros x N1 N2 N3. apply AGm. apply (outside_hdr V x V0); lia. }
      destruct W0 as [AI0' MI0'].
      assert (DATA0 : forall i, (0 <= i < L)%Z -> M0 (Z_to_bv 64 (b + i)) = Some (nth (Z.to_nat i) data (Z_to_bv 8 0))).
      { intros i Hi. rewrite AGm; [apply DATA; exact Hi|]. apply (outside_hdr V _ V0); rewrite u64 by lia; lia. }
      apply (malloc_part k b V R0 M0 md A); try assumption; try (unfold plen in *; lia).
      refine (regs_ok_pin _ _ _ (21%bv : reg) (EVar 25) HR _). regv HR (21%bv : reg). cbn [edenot ev ENV]. rewrite V12, rd8_u, calls_val, V25 by lia.
      unfold calls. rewrite (proj2 (Z.eqb_neq _ _) Hc0). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="L LIBOK limg_intro limg Hlimg limg_hi limg_lo Hplen Htid HCEIL Hvsp"] Theorem body_ok_holds : body_ok sp0 a0s path envv rdraw tid mem0 fs0 data.
  Proof.
    intros k b vals R M md A ST HLc.
    pose proof ST as [_ _ _ _ _ _ _ _ _ _ _ _ BUF _]. pose proof BUF as [_ _ _ _ Hk _ _].
    pose proof (cap_range path data Hplen k Hk) as Hcap. pose proof cfg_range as Hcfg.
    pose proof (dbyte_range data 0) as B0. pose proof (dbyte_range data 1) as B1. pose proof (dbyte_range data 2) as B2.
    unfold t_body.
    replace (MAX_INPUT <=? Z.of_nat (length data))%Z with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; unfold L in HLc; lia).
    destruct (Nat.ltb_spec (length data) 6) as [H6|H6].
    { apply (hdr_short sp0 a0s path envv rdraw tid mem0 fs0 data Hvsp HCEIL Htid Hplen k b vals R M md A ST HLc). lia. }
    cbv zeta.
    set (cw := (bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0)))%Z).
    assert (Ecfg : Z.to_nat (cw mod 32768) = Z.to_nat cfg) by (subst cw; unfold cfg, DU_Hcqt.cfg, cfgv, dbyte; reflexivity).
    rewrite Ecfg.
    destruct (Nat.ltb_spec (length data) (6 + Z.to_nat cfg)) as [Ho|Ho].
    { apply (hdr_overrun sp0 a0s path envv rdraw tid mem0 fs0 data Hvsp HCEIL Htid Hplen k b vals R M md A ST HLc); [lia|].
      unfold cfg, DU_Hcqt.cfg in *. lia. }
    (* [comment removed for export] *)
    pose proof (hdr_run k b vals R M md A ST HLc ltac:(unfold cfg, DU_Hcqt.cfg in *; lia)) as RUN.
    unfold succ, calls in RUN.
    destruct (Z.eqb_spec cfg 0) as [Hc0|Hc0].
    - rewrite Hc0. cbn [Z.to_nat] in RUN |- *. exact RUN.
    - destruct (Z.to_nat cfg) as [|c] eqn:Ec; [exfalso; lia|].
      replace (S (Z.to_nat (bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4))) with (Z.to_nat (dbyte data 2 mod 4 + 1)) by (unfold dbyte; pose proof (Z.mod_pos_bound (dbyte data 2) 4 ltac:(lia)); unfold dbyte in *; lia).
      exact RUN.
  Qed.
End Header.
End DU_Hk2b.

Module DU_Mzdi.
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
From OssFuzzTheorems.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec ShapeAlg Spec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_S6f3 DU_M1ef.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Dir.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_T0kc.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Dir LibIface.
Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Amb OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_S6f3 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_M1ef OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Dir.DU_Loop OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Dir.DU_Main OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_T0kc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.DU_Hk2b OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_Dir OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibIface.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU DriverKit.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.

(* [comment removed for export] *)
Section Top.
  Context {Clg : Ceiling} {AI : AllocSpec LayoutPU} {DK : DriverKit LayoutPU InitPU}.
  Variables limg_lo limg_hi : Z.
  Hypothesis Hlimg : (0x10000 <= limg_lo)%Z /\ (limg_hi <= 0x31a38)%Z.
  Variable limg : (word -> option byte) -> Prop.
  Hypothesis limg_intro : forall m, Mem.mem_inv RSEGS m ->
    (forall i, (limg_lo <= i < limg_hi)%Z -> m (Z_to_bv 64 i) = None) -> limg m.
  Hypothesis LIBOK : lib_call_ok (LLU limg_lo limg_hi limg limg_intro).

  Lemma body_all_holds : body_all.
  Proof.
    intros AMB sp0 a0s path envv rdraw tid regs0 mem0 fs0 fdata Hva Hve Hvsp HCEIL Htid ME Hfile Hplen.
    exact (body_ok_holds sp0 a0s path envv rdraw tid mem0 fs0 fdata Hvsp HCEIL Htid Hplen limg_lo limg_hi Hlimg limg limg_intro LIBOK).
  Qed.

  Theorem ref_realizes_spec_lib :
    forall sp brk mbase rdraw (inp : ProcInput),
      valid_sp sp -> alloc_ceiling = (bv_unsigned sp - 8388608)%Z ->
      valid_brk rsegs brk ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      in_abort_terminal inp = false ->
      realizes rsegs
        (init_config rsegs rpc rph sp brk mbase rdraw DU_Mz0p.LIM inp)   (* [comment removed for export] *)
        (spec (in_argv inp) (in_fs inp)).
  Proof. exact (ref_realizes_spec dir_ok_holds body_all_holds). Qed.
End Top.

(* [comment removed for export] *)
Theorem ref_realizes_spec_lib_run {BW : BWorld}
    (AIc : forall Clg : Ceiling, @AllocSpec Clg LayoutPU)
    (DKc : forall Clg : Ceiling, @DriverKit Clg LayoutPU InitPU (AIc Clg))
    (limg_lo limg_hi : Z) (Hlimg : (0x10000 <= limg_lo)%Z /\ (limg_hi <= 0x31a38)%Z)
    (limg : (word -> option byte) -> Prop)
    (limg_intro : forall m, Mem.mem_inv RSEGS m ->
       (forall i, (limg_lo <= i < limg_hi)%Z -> m (Z_to_bv 64 i) = None) -> limg m)
    (LIBOK : forall Clg : Ceiling, @lib_call_ok Clg (LLU limg_lo limg_hi limg limg_intro) (AIc Clg)) :
  forall sp brk mbase rdraw (inp : ProcInput) (Hsp : valid_sp sp),
    valid_brk rsegs brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    in_abort_terminal inp = false ->
    realizes rsegs
      (init_config rsegs rpc rph sp brk mbase rdraw bw_lim inp)   (* [comment removed for export] *)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rdraw inp Hsp Hbrk Hva Hve Hfit Hab.
  apply (@ref_realizes_spec_lib (ceiling_of_sp (BW:=BW) sp Hsp) (AIc _) (DKc _) limg_lo limg_hi Hlimg limg limg_intro (LIBOK _) sp brk mbase rdraw inp Hsp);
    try assumption.
  unfold alloc_ceiling, ceiling_of_sp. rewrite stack_max_size_val. reflexivity.
Qed.
End DU_Mzdi.

Import OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.ShapeEF OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Spec OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.LibIface OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.D_TrLoop OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.D_Mak2g OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.DU_T0kc OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.DU_Mzdi.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 LayoutPU DriverKit.
Local Open Scope Z_scope.

Definition SRC0 : Image :=
  mkImage OssFuzzTheorems.varnish.esi_parse_fuzzer.images.Plain.M.loaded_segments
          OssFuzzTheorems.varnish.esi_parse_fuzzer.images.Plain.M.init_pc
          OssFuzzTheorems.varnish.esi_parse_fuzzer.images.Plain.M.phdrs.

Definition UBSAN : Image :=
  mkImage OssFuzzTheorems.varnish.esi_parse_fuzzer.images.Ubsan.M.loaded_segments
          OssFuzzTheorems.varnish.esi_parse_fuzzer.images.Ubsan.M.init_pc
          OssFuzzTheorems.varnish.esi_parse_fuzzer.images.Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition LL0 : LibLayout :=
  mkLibLayout LayoutP0 0x18048 0x41830 img_ok0 0x30270 0x31580 img_ok0_intro 0x623c8.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma source_le_target_alloc_limit : State.source_alloc_limit <= State.target_alloc_limit.
Proof. unfold State.source_alloc_limit, State.target_alloc_limit. lia. Qed.
Definition bw_target : BWorld :=
  {| bw_on := false; bw_lim := State.target_alloc_limit; bw_lim_ok := source_le_target_alloc_limit |}.

From OssFuzzTheorems.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Section Assembly.
  (* [comment removed for export] *)
  Variable AI0 : forall Clg : Ceiling, @AllocSpec Clg LayoutP0.
  Variable DK0 : forall Clg : Ceiling, @DriverKit Clg LayoutP0 InitP0 (AI0 Clg).
  Variable AIU : forall Clg : Ceiling, @AllocSpec Clg LayoutPU.
  Variable DKU : forall Clg : Ceiling, @DriverKit Clg LayoutPU InitPU (AIU Clg).

  (* [comment removed for export] *)
  Hypothesis LIB0 : forall Clg : Ceiling, @lib_call_ok Clg LL0 (AI0 Clg).

  (* [comment removed for export] *)
  Variables limg_lo limg_hi : Z.
  Hypothesis Hlimg : 0x10000 <= limg_lo /\ limg_hi <= 0x31a38.
  Variable limg : (word -> option byte) -> Prop.
  Hypothesis limg_intro : forall m,
    Mem.mem_inv OssFuzzTheorems.varnish.esi_parse_fuzzer.images.Ubsan.M.loaded_segments m ->
    (forall i, limg_lo <= i < limg_hi -> m (Z_to_bv 64 i) = None) -> limg m.
  Hypothesis LIBU : forall Clg : Ceiling,
    @lib_call_ok Clg (DU_T0kc.LLU limg_lo limg_hi limg limg_intro) (AIU Clg).

  Theorem ubsan_base : strong_universal_error_free_T_scfg ACFG SRC0 UBSAN.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    (* [comment removed for export] *)
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    (* [comment removed for export] *)
    (first [ dand10 Hvalid as Hargv Henvp Hfs Hrel Hcreds Hnofile Hsigmask Hhwcap Habort _ | destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & Hcreds & Hnofile & Hsigmask & Hhwcap & Habort & _) ]).
    apply (shape_strong_equiv_ef _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - exact (D_Mak2g.ref_realizes_spec_lib_run AI0 DK0 img_ok0 img_ok0_intro LIB0
               rsp rbrk rmb rrnd inp Hrsp Hrbrk Hargv Henvp Hrfit Habort).
    - (* [comment removed for export] *)
      apply rz_of_core.
      exact (rz_unwrap _ _ _ (DU_Mzdi.ref_realizes_spec_lib_run (BW:=bw_target) AIU DKU limg_lo limg_hi Hlimg limg limg_intro LIBU
               asp abrk amb arnd inp Hasp Habrk Hargv Henvp Hafit Habort)
               (never_excused_off (BW:=bw_target) _ eq_refl _)).
  Qed.

  (* [comment removed for export] *)
  Theorem plain_halts : halts_allowed_T_scfg ACFG AnyExit.codes SRC0.
  Proof.
    apply (halts_of_realizes _ _ _ (fun inp => spec (in_argv inp) (in_fs inp))
             (fun inp => tgood_spec (in_argv inp) (in_fs inp))).
    intros sp brk mbase rdraw inp Hen Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
    destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    destruct Hvalid as (Hargv & Henvp & _ & _ & _ & _ & _ & _ & Habort & _).
    exact (D_Mak2g.ref_realizes_spec_lib_run (BW:=bw_pinned) AI0 DK0 img_ok0 img_ok0_intro LIB0
             sp brk mbase rdraw inp Hsp Hbrk Hargv Henvp Hfit Habort).
  Qed.

  Theorem ubsan_halts : halts_allowed_T_scfg ACFG AnyExit.codes UBSAN.
  Proof.
    apply (halts_of_realizes _ _ _ (fun inp => spec (in_argv inp) (in_fs inp))
             (fun inp => tgood_spec (in_argv inp) (in_fs inp))).
    intros sp brk mbase rdraw inp Hen Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
    destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    destruct Hvalid as (Hargv & Henvp & _ & _ & _ & _ & _ & _ & Habort & _).
    exact (DU_Mzdi.ref_realizes_spec_lib_run (BW:=bw_pinned) AIU DKU limg_lo limg_hi Hlimg limg limg_intro LIBU
             sp brk mbase rdraw inp Hsp Hbrk Hargv Henvp Hfit Habort).
  Qed.
End Assembly.
