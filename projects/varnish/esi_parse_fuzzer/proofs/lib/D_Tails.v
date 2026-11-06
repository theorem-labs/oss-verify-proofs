(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm D_Li6dm Spec LibWbxd RefNodes D_Exvwg D_Stqgu D_Exit RefMocc D_Stmwg D_Manqc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MemSplit D_Kn21w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.

Module D_Oobk0.
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
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm D_Li6dm Spec LibWbxd RefNodes D_Exvwg D_Stqgu D_Exit RefMocc D_Stmwg D_Manqc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MemSplit D_Kn21w D_Alu7n.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ALLOC_STATICS_HI : Z := STATICS_HI.
(* [comment removed for export] *)
Definition knBx : list kentry := knB ++ kimg_pieces [(ALLOC_STATICS_HI, HEAP_LO)].
(* [comment removed for export] *)
Definition kwr_data : kentry := KWr (SA (ELit 0) 0x31000) 0x32000.   (* [comment removed for export] *)
Lemma kwr_data_ok : forall E M, kentry_ok RSEGS E M kwr_data.
Proof.
  intros E M. cbn [kentry_ok]. split.
  - unfold flat, estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia. lia.
  - intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
    apply store_ok_data; rewrite u_small by lia; lia.
Qed.
Definition knM0 : list kentry := Eval vm_compute in (kn_keep2 knBx (RS_call (-128) MALLOC_STACK) VICT ++ [kwr_data]).

(* [comment removed for export] *)
Definition srM0 : list expr := Eval vm_compute in sr_after_call_j srB (map ridx callee_saved) 38.
Definition srM0z : list expr := Eval vm_compute in sr_upd srM0 (ridx 10) (ELit 0).

Lemma knB_has_img : In (KImg STATICS_LO HEAP_LO) knB.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section Leaf.
  Variables a0s path : list byte.
  Variable rdraw : EntryDraw.
  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path rdraw)).
End Leaf.
End D_Oobk0.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n.

Module D_Dr084.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv ShapeAlg Shapi1s Nodes MmapSim AgentLib Frame SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymAux LibK2dm RefMocc D_Kn21w Spec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Stmwg D_Manqc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n D_Li6dm D_Wamxh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NB : nat := 38.
Definition jx (i : nat) : expr := EVar (NB + i).

(* [comment removed for export] *)
Definition sr_drv : list expr :=
  Eval cbv in [ELit 0; jx 1; spx (-128); ELit 0x10800; ELit 0x42158; jx 5; jx 6; jx 7;
   ELit 2; jx 9; jx 10; jx 11; jx 12; jx 13; jx 14; jx 15; jx 16; jx 17;
   EVar 2; jx 19; ELit 3; jx 21; jx 22; jx 23; ELit 0; ELit 0; ELit 0; ELit 0; jx 28; jx 29; jx 30; jx 31].

(* [comment removed for export] *)
Record pins_main (sp0 p1 : word) (R : bvmap 5 word) : Prop := PINS {
  pn_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  pn_gp : getr R 3 = Z_to_bv 64 0x10800;
  pn_tp : getr R 4 = Z_to_bv 64 0x42158;
  pn_s0 : getr R 8 = Z_to_bv 64 2;
  pn_s2 : getr R 18 = p1;
  pn_s4 : getr R 20 = Z_to_bv 64 3;
  pn_s8 : getr R 24 = Z_to_bv 64 0;
  pn_s9 : getr R 25 = Z_to_bv 64 0;
  pn_s10 : getr R 26 = Z_to_bv 64 0;
  pn_s11 : getr R 27 = Z_to_bv 64 0 }.

(* [comment removed for export] *)
Definition knD : list kentry := knM0.

Lemma knD_vars : kn_vars_lt 6 knD = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition knD_iw : nat := Eval vm_compute in match kindex (is_kwr_cov (EVar 0) (-8388608) 8388608) knD 0 with Some i => i | None => 0%nat end.
Lemma knD_win : nth_error knD knD_iw = Some (KWr (SA (EVar 0) (-8388608)) 8388608). Proof. vm_compute. reflexivity. Qed.

Section Drv.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Hypothesis Hvsp : valid_sp sp0.

  Definition base_ok (vals : list word) : Prop :=
    length vals = 70%nat /\ vals_ev vals 0 = sp0 /\ vals_ev vals 1 = p0 sp0 a0s path envv
    /\ vals_ev vals 2 = p1 sp0 a0s path envv /\ vals_ev vals 5 = tid.

  (* [comment removed for export] *)
  Definition junk_at (vals : list word) (R : bvmap 5 word) : Prop :=
    forall i, (i < 32)%nat -> vals_ev vals (NB + i) = getr R (Z_to_bv 5 (Z.of_nat i)).

  Lemma junk_at_app : forall base R, length base = NB -> junk_at (base ++ junk_vals R) R.
  Proof.
    intros base R HL i Hi. unfold vals_ev. rewrite <- HL, app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma sr_drv_ok : forall vals R,
    base_ok vals -> junk_at vals R -> pins_main sp0 (p1 sp0 a0s path envv) R ->
    regs_ok (ENV a0s path rdraw vals) sr_drv R.
  Proof.
    (intros vals R; (first [ intro dR_1; dand5 dR_1 as HL V0 V1 V2 V5 | intros (HL & V0 & V1 & V2 & V5) ]); intros HJ [P2 P3 P4 P8 P18 P20 P24 P25 P26 P27]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (u64_range sp0).
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_drv all_regs];
      try (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
             change (edenot (ENV a0s path rdraw vals) (EVar n)) with (vals_ev vals n);
             first [ let i := eval vm_compute in (n - 38)%nat in
                     etransitivity; [| symmetry; exact (HJ i ltac:(lia))]; f_equal; apply bv_eq; reflexivity
                   | rewrite V2; exact P18 ] end).
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

  (* [comment removed for export] *)
  Definition junkify_ok (sr sr' : list expr) : bool :=
    (Nat.eqb (length sr') 32 && expr_eqb (nth 0 sr' (ELit 0)) (ELit 0) &&
     forallb (fun i => expr_eqb (nth i sr' (ELit 0)) (nth i sr (ELit 0)) || expr_eqb (nth i sr' (ELit 0)) (EVar (NB + i)))
             (seq 1 31))%bool.

  Lemma regs_ok_junkify : forall vals R sr sr',
    junk_at vals R -> regs_ok (ENV a0s path rdraw vals) sr R -> junkify_ok sr sr' = true ->
    regs_ok (ENV a0s path rdraw vals) sr' R.
  Proof.
    intros vals R sr sr' HJ HR Hok. unfold junkify_ok in Hok. apply andb_prop in Hok as [Hok Hall].
    apply andb_prop in Hok as [Hlen H0]. apply Nat.eqb_eq in Hlen. apply expr_eqb_eq in H0.
    apply regs_ok_by_index. intros i Hi. rewrite nth_all_regs by exact Hi.
    destruct i as [|i]; [rewrite H0; reflexivity|].
    pose proof (proj1 (forallb_forall _ _) Hall (S i) ltac:(apply in_seq; lia)) as Hb. cbn beta in Hb.
    apply orb_prop in Hb as [Hb|Hb]; apply expr_eqb_eq in Hb; rewrite Hb.
    - rewrite (HR (Z_to_bv 5 (Z.of_nat (S i)))), sr_get_nat by lia. reflexivity.
    - cbn [edenot ev ENV]. symmetry. apply HJ. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma pins_of_sr_drv : forall vals R,
    base_ok vals -> regs_ok (ENV a0s path rdraw vals) sr_drv R -> pins_main sp0 (p1 sp0 a0s path envv) R.
  Proof.
    (intros vals R; (first [ intro dR_2; dand5 dR_2 as HL V0 V1 V2 V5 | intros (HL & V0 & V1 & V2 & V5) ]); intros HR). pose proof (proj1 Hvsp) as SPlo. pose proof (u64_range sp0).
    split.
    - regv HR (2%bv : reg). rewrite edenot_add_lit. unfold adenot, v_addi.
      cbn [a_base a_off edenot ev ENV]. change (SymRun.vals_ev vals 0) with (vals_ev vals 0). rewrite V0. f_equal; lia.
    - regv HR (3%bv : reg). reflexivity.
    - regv HR (4%bv : reg). reflexivity.
    - regv HR (8%bv : reg). reflexivity.
    - regv HR (18%bv : reg). cbn [edenot ev ENV]. exact V2.
    - regv HR (20%bv : reg). reflexivity.
    - regv HR (24%bv : reg). reflexivity.
    - regv HR (25%bv : reg). reflexivity.
    - regv HR (26%bv : reg). reflexivity.
    - regv HR (27%bv : reg). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition pins_expr_ok (sr : list expr) : bool :=
    (expr_eqb (nth 2 sr (ELit 0)) (EAlu ALU_ADD (EVar 0) (ELit (-128))) &&
     expr_eqb (nth 3 sr (ELit 0)) (ELit 0x10800) && expr_eqb (nth 4 sr (ELit 0)) (ELit 0x42158) &&
     expr_eqb (nth 8 sr (ELit 0)) (ELit 2) && expr_eqb (nth 18 sr (ELit 0)) (EVar 2) &&
     expr_eqb (nth 20 sr (ELit 0)) (ELit 3) &&
     expr_eqb (nth 24 sr (ELit 0)) (ELit 0) && expr_eqb (nth 25 sr (ELit 0)) (ELit 0) &&
     expr_eqb (nth 26 sr (ELit 0)) (ELit 0) && expr_eqb (nth 27 sr (ELit 0)) (ELit 0))%bool.

  Lemma pins_of_sr : forall vals R sr,
    vals_ev vals 0 = sp0 -> vals_ev vals 2 = p1 sp0 a0s path envv -> pins_expr_ok sr = true ->
    regs_ok (ENV a0s path rdraw vals) sr R -> pins_main sp0 (p1 sp0 a0s path envv) R.
  Proof.
    intros vals R sr V0 V2 Hok HR. pose proof (proj1 Hvsp) as SPlo. pose proof (u64_range sp0).
    unfold pins_expr_ok in Hok. repeat (apply andb_prop in Hok as [Hok ?]).
    repeat match goal with G : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in G end.
    Ltac pin HR r n := rewrite (HR r);
                       lazymatch goal with |- edenot _ (sr_get ?srx _) = _ =>
                         change (sr_get srx r) with (nth n srx (ELit 0));
                         match goal with G : nth n srx _ = _ |- _ => rewrite G end end.
    split.
    - pin HR (2%bv : reg) 2%nat. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
      change (SymRun.vals_ev vals 0) with (vals_ev vals 0). rewrite V0. f_equal; lia.
    - pin HR (3%bv : reg) 3%nat. reflexivity.
    - pin HR (4%bv : reg) 4%nat. reflexivity.
    - pin HR (8%bv : reg) 8%nat. reflexivity.
    - pin HR (18%bv : reg) 18%nat. cbn [edenot ev ENV]. exact V2.
    - pin HR (20%bv : reg) 20%nat. reflexivity.
    - pin HR (24%bv : reg) 24%nat. reflexivity.
    - pin HR (25%bv : reg) 25%nat. reflexivity.
    - pin HR (26%bv : reg) 26%nat. reflexivity.
    - pin HR (27%bv : reg) 27%nat. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma env_agree_rejunk : forall vals R' ebs, (NB <= length vals)%nat ->
    env_agree NB (Env (vals_ev vals) ebs) (Env (vals_ev (firstn NB vals ++ junk_vals R')) ebs).
  Proof.
    intros vals R' ebs HL. split; [|reflexivity]. intros i Hi. cbn [ev].
    assert (HLf : length (firstn NB vals) = NB) by (rewrite length_firstn; lia).
    unfold vals_ev. rewrite app_nth1 by (rewrite HLf; exact Hi). rewrite nth_firstn. apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity.
  Qed.
End Drv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cap (k : nat) : Z := (65536 * 2 ^ (Z.of_nat k))%Z.

(* [comment removed for export] *)
Fixpoint lshape (data : list byte) (fs : Fs.Fs) (fuel : nat) (k : nat) (len : Z) : TSet :=
  match fuel with
  | O => t_nil
  | S f =>
      let L := Z.of_nat (length data) in
      if (len =? cap k)%Z then
        if (10 <=? Z.of_nat k)%Z then t_die msg_refused fs
        else lshape data fs f (S k) len    (* [comment removed for export] *)
      else
        let n := Z.min (Z.min (cap k - len) 65536) (L - len) in
        if (n =? 0)%Z then t_body data fs
        else lshape data fs f k (len + n)
  end.

(* [comment removed for export] *)
Lemma lshape_opened : forall data fs f k len,
  (Z.of_nat (length data) - len + 11 - Z.of_nat k < Z.of_nat f)%Z ->
  (k <= 10)%nat -> (0 <= len <= cap k)%Z -> (len <= Z.of_nat (length data))%Z ->
  (len = cap k \/ cap k <= 2 ^ 26)%Z ->
  t_eq (lshape data fs f k len) (t_opened data fs).
Proof.
  intros data fs f. induction f as [|f IH]; intros k len Hf Hk Hlen HL Hcap; [lia|].
  cbn [lshape]. set (L := Z.of_nat (length data)) in *.
  assert (CAPk : (cap k <= 2 ^ 26)%Z).
  { destruct Hcap as [->|H]; [|exact H]. unfold cap. 
    assert (2 ^ Z.of_nat k <= 2 ^ 10)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 26)%Z with (65536 * 2 ^ 10)%Z. lia. }
  destruct (Z.eqb_spec len (cap k)) as [E|NE].
  - destruct (Z.leb_spec 10 (Z.of_nat k)) as [K10|K10].
    + (* [comment removed for export] *)
      assert (k = 10)%nat by lia. subst k. unfold t_opened, t_body.
      change (cap 10) with 67108864%Z in E.
      replace (MAX_INPUT <=? Z.of_nat (length data))%Z with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
      apply t_eq_refl.
    + (* [comment removed for export] *)
      apply IH; try lia.
      * unfold cap in *. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
      * right. unfold cap in *. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        assert (2 ^ Z.of_nat k <= 2 ^ 9)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 26)%Z with (65536 * (2 * 2 ^ 9))%Z. lia.
  - set (n := Z.min (Z.min (cap k - len) 65536) (L - len)).
    destruct (Z.eqb_spec n 0) as [N0|N0].
    + (* [comment removed for export] *)
      assert (len = L) by (subst n; lia). unfold t_opened. apply t_eq_refl.
    + apply IH; subst n; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RS_heap : list frange :=
  [(ELit 0, HEAP_LO, (HEAP_HI - HEAP_LO)%Z); (EVar 0, (-8388608 - CSLACK)%Z, CSLACK); (ELit 0, LOW_LO, (LOW_HI - LOW_LO)%Z)].
Lemma knD_heap_incl : kn_incl knD (kn_keep2 knD RS_heap []) = true. Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition STAGE : Z := 0x317f9.
Definition RS_stage : list frange := [(ELit 0, STAGE, 65536%Z)].
(* [comment removed for export] *)
Lemma knD_main_incl : kn_incl knD (kn_keep2 knD (RS_call (-128) 8192) VICT ++ [kwr_data]) = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition out_heap (sp0 x : word) : Prop :=
  ~ (HEAP_LO <= bv_unsigned x < HEAP_HI)%Z
  /\ ~ (bv_unsigned sp0 - 8388608 - CSLACK <= bv_unsigned x < bv_unsigned sp0 - 8388608)%Z
  /\ ~ (LOW_LO <= bv_unsigned x < LOW_HI)%Z.

Lemma know_knD_heap : forall E M M',
  know_ok RSEGS E M knD ->
  (0x7fff80000000 <= bv_unsigned (ev E 0))%Z ->
  (forall x : word, out_heap (ev E 0) x -> M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' knD.
Proof.
  intros E M M' HK Hsp OUT G. apply (know_ok_incl RSEGS E M' knD _ knD_heap_incl).
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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma know_knD_main_call : forall E M', (forall E' M0, kentry_ok RSEGS E' M0 kwr_data) ->
  know_ok RSEGS E M' (kn_keep2 knD (RS_call (-128) MALLOC_STACK) VICT) -> know_ok RSEGS E M' knD.
Proof.
  intros E M' KW HK. apply (know_ok_incl RSEGS E M' knD _ knD_main_incl).
  apply know_ok_app; [exact HK | constructor; [apply KW | constructor]].
Qed.
(* [comment removed for export] *)
End D_Dr084.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Wamxh SymAux RefPl89.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Definition STOPS_T : list Z := [0x25d58; 0x2299c]%Z.
Definition FUEL_T : nat := 20000.
Definition runT (dirs : list bool) (ss : sym_state) := sym_exec RSEGS FUEL_T true STOPS_T (SCR dirs [] []) ss [].
Definition kn_afterT (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Tactic Notation "run_blockT" constr(dirs) constr(NX) := run_block_gen FUEL_T STOPS_T (SCR dirs [] []) NX false.
Definition no_res : stdio_res := SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dirsF : list bool := [false; false; false; true; false].
Definition rF1 := Eval vm_compute in runT dirsF (SS 0x17dac sr_drv [] knD 70).
Definition srF1 : list expr := Eval vm_compute in s_regs (fst (fst rF1)).
Definition knF1 : list kentry := Eval vm_compute in kn_afterT rF1 knD.
Definition resF : stdio_res := Eval vm_compute in match stdio_call 70 srF1 knF1 with Some r => r | None => no_res end.
Lemma resF_eq : stdio_call 70 srF1 knF1 = Some resF. Proof. vm_compute. reflexivity. Qed.
Definition srF3_0 : list expr := Eval vm_compute in sc_sr resF.
Definition knF3_0 : list kentry := Eval vm_compute in sc_kn resF.
Definition rF3 := Eval vm_compute in runT [] (SS (sc_ret resF) srF3_0 [] knF3_0 102).
Definition knF3 : list kentry := Eval vm_compute in kn_afterT rF3 knF3_0.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma msgF_bytes : kread_bytes RSEGS knF1 (EVar 0) (-560) 38 =
  Some [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10]%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_refused_eq : map (fun z => Z_to_bv 8 z)
  [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10]%Z
  = msg_refused.
Proof. vm_compute. reflexivity. Qed.
Section Tails.
  Context {AMB : Amb}.
  Context {BW : BWorld}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.

  (* [comment removed for export] *)
  Ltac exit_leaf vals' HL P0 HR HK Hh Hlazy knE wp2 :=
    apply ref_exit_Z;
    pose proof (know_nth RSEGS _ _ knE ltac:(let i := kidx knE (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid;
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x42158), (bv_unsigned (vals_ev vals' 5)),
           (Z_to_bv 64 wp2), (Z_to_bv 64 0), false;
    split; [|split; [unfold atexit_st; krd_solve HK|split; [exact Hh|split; [exact Hlazy|]]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV]; rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        pose proof (kwr_store_ok RSEGS _ _ knE ltac:(let i := kidx knE (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; lia
      | lit_u; lia
      | lia
      | lit_u; change (270680 - 168)%Z with 0x420b0%Z;
        let Htc := fresh in krd HK 0x420b0%Z 4%nat Htc; rewrite Htc; cbn [ev ENV];
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | krd_solve HK | krd_solve HK   (* [comment removed for export] *)
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ].

  #[using="Hvsp"] Theorem refused_tail : forall vals R (M : word -> option byte) (md : Model),
    base_ok sp0 a0s path envv tid vals -> junk_at vals R -> pins_main sp0 (p1 sp0 a0s path envv) R ->
    know_ok RSEGS (ENV a0s path rdraw vals) M knD ->
    m_halted md = None -> m_vm_lazy md = [] ->
    fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17dac) M (seg_rom RSEGS)) md) (t_die msg_refused (m_fs md)).
  Proof.
    intros vals R M md HB HJ HP HK Hh Hlazy Hfd2.
    pose proof HB as (HL & P0 & P1 & P2 & P5).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (sr_drv_ok sp0 a0s path envv rdraw tid Hvsp vals R HB HJ HP) as HR. clear HJ HP.
    run_blockT dirsF 70%nat.
    (* [comment removed for export] *)
    1-5: cbn [sc_denot edenot ev ENV]; rewrite P0; rewrite <- (Z_to_bv_bv_unsigned 64 sp0);
         apply bt_and3; [lia|]; cbv beta iota;
         rewrite (mod4_shift (bv_unsigned sp0) _ 0) by (rewrite <- (Z.mod_mod_divide _ 16 4) by (exists 4%Z; reflexivity); rewrite SPal; reflexivity);
         reflexivity.
    unfold t_die, W.
    apply (stdio_call_sound vals (blobs_ev (blobs0 a0s path rdraw)) srF1 knF1 R M md resF msg_refused []
             (t_exit (exit_code 2) (m_fs md)) HR HK (eq_trans (f_equal (fun n => stdio_call n srF1 knF1) HL) resF_eq));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resF];
      change (Z.of_nat (length msg_refused)) with 38%Z; change (Z.of_nat (@length byte [])) with 0%Z.
    - rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. rewrite !u_small by lia. lia.
    - rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. rewrite !u_small by lia. lia.
    - cbn [edenot]. reflexivity.
    - lia.
    - right. rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. rewrite !u_small by lia. lia.
    - left. rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. lit_u. rewrite !u_small by lia. lia.
    - cbn [edenot]. lit_u. lia.
    - rewrite edenot_add_lit. rewrite <- msg_refused_eq. change (length (map _ _)) with 38%nat.
      rewrite Z_to_bv_bv_unsigned.
      apply (rdn_of_kread_bytes RSEGS _ M knF1 (EVar 0) 38 (-560) _ HK msgF_bytes).
      unfold flat, estart. cbn [a_base a_off edenot ev ENV]. rewrite P0. lia.
    - reflexivity.
    - exact Hfd2.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK R M. intros R M HR HK.
      change (sc_sr resF) with srF3_0 in HR. change (sc_kn resF) with knF3_0 in HK.
      set (vals' := vals ++ junk_vals R) in *.
      assert (HL' : length vals' = 102%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals'. clear HL P0. rename HL' into HL. rename P0' into P0.
      change (Env (vals_ev vals') (blobs_ev (blobs0 a0s path rdraw))) with (ENV a0s path rdraw vals') in HR, HK.
      run_blockT (@nil bool) 102%nat.
      apply (rz_conseq RSEGS _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs md)))).
      2:{ apply exit_leaf_eq. lia. }
      exit_leaf vals' HL P0 HR HK Hh Hlazy knF3 0%Z.
  Qed.
End Tails.
