(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk MemSplit ShapeAlg Nodes RefNodes SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymDriveS2 S1SpecConsts S1Spec U1ExitKn U1ExitDefs U1Exit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u1_exit_u_Z {fx : FPState} : forall regs mem model code,
  exit_pre_u regs mem model code ->
  srealizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 EXIT) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros. replace (Z_to_bv 64 EXIT) with (0xd1e54 : word) by (apply bv_eq; reflexivity).
  apply u1_exit_u. assumption.
Qed.

Lemma u1_exit_u1_Z {fx : FPState} : forall regs mem model code,
  exit_pre_u1 regs mem model code ->
  srealizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 EXIT) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros. replace (Z_to_bv 64 EXIT) with (0xd1e54 : word) by (apply bv_eq; reflexivity).
  apply u1_exit_u1. assumption.
Qed.

Lemma u1_exit_t0_Z {fx : FPState} : forall regs mem model code,
  exit_pre_t0 regs mem model code ->
  srealizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 EXIT) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros. replace (Z_to_bv 64 EXIT) with (0xd1e54 : word) by (apply bv_eq; reflexivity).
  apply u1_exit_t0. assumption.
Qed.

Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Lemma mod16_sub : forall a k, (a mod 16 = 0)%Z -> (k mod 16 = 0)%Z -> ((a - k) mod 16 = 0)%Z.
Proof.
  intros a k Ha Hk. rewrite Zminus_mod, Ha, Hk. reflexivity.
Qed.

Lemma kimg_clear : forall segs E M kn i lo hi (a b : Z),
  know_ok segs E M kn -> nth_error kn i = Some (KImg lo hi) ->
  (lo <= a)%Z -> (b <= hi)%Z -> img_clear M a b.
Proof.
  intros segs E M kn i lo hi a b HK Hn Ha Hb x Hx.
  pose proof (know_nth segs E M kn i _ HK Hn) as (_ & _ & Hnone). apply Hnone. lia.
Qed.

Ltac zclosed := first [ solve [apply Nat.leb_le; reflexivity] | solve [apply Z.leb_le; reflexivity]
                      | solve [apply Z.ltb_lt; reflexivity] | lia ].
Ltac krdF HK a n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (ELit 0) a n) in
    lazymatch r with
    | Some ?v =>
        pose proof (kread_rdn segs E M kn (ELit 0) a n v HK
                      ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(zclosed) ltac:(zclosed)
                      ltac:(unfold flat, estart; cbn [a_base a_off edenot];
                            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; repeat split; zclosed)) as H;
        rewrite adenot_lit0 in H; cbn [edenot] in H
    | None => fail "krdF: knowledge does not determine this read"
    end
  end.
Ltac krd_solveF HK :=
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some _ =>
      let H := fresh "Hrd" in
      krdF HK a n H; rewrite H; clear H;
      first [ reflexivity | rewrite ?Z_to_bv_bv_unsigned; reflexivity | idtac ]
  end.

Definition cell_kn_b (segs : list Segment) (kn : list kentry) (c : Z * nat * Z) : bool :=
  match c with (a, w, v) =>
    match kread segs kn (ELit 0) a w with
    | Some (ELit z) => (Z.eqb z v && Nat.leb 1 w && Nat.leb w 8 && (0 <=? a) && (a + Z.of_nat w <=? 2 ^ 64))%Z%bool
    | _ => false
    end
  end.
Lemma cells_of_kn : forall segs E M kn (cells : list (Z * nat * Z)), know_ok segs E M kn ->
  forallb (cell_kn_b segs kn) cells = true ->
  Forall (fun c : Z * nat * Z => match c with (a, w, v) =>
    rdn segs M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)) end) cells.
Proof.
  intros segs E M kn cells HK. induction cells as [|[[a w] v] rest IH]; intros Hb; [constructor|].
  cbn [forallb] in Hb. apply andb_prop in Hb as [Hc Hrest].
  constructor; [|apply IH; exact Hrest].
  unfold cell_kn_b in Hc.
  destruct (kread segs kn (ELit 0) a w) as [e|] eqn:Hr; [|discriminate Hc].
  destruct e as [z| | | | | | |]; try (cbn in Hc; discriminate Hc).
  apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2].
  apply andb_prop in Hc as [Hz H1]. apply Z.eqb_eq in Hz. subst z.
  apply Nat.leb_le in H1. apply Nat.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  pose proof (kread_rdn segs E M kn (ELit 0) a w (ELit v) HK Hr H1 H2
                ltac:(unfold flat, estart; cbn [a_base a_off edenot];
                      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as H.
  rewrite adenot_lit0 in H. cbn [edenot] in H. exact H.
Qed.

Ltac kimg_clear_solve HK :=
  lazymatch goal with |- img_clear ?M ?a ?b =>
  lazymatch type of HK with know_ok ?segs ?E _ ?kn =>
    let i := kidx kn (is_kimg_cov a (b - a)%Z) in
    eapply (kimg_clear segs E M kn i); [exact HK | reflexivity | lia | lia]
  end end.

Ltac close_exit_u_core_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- srealizes _ (mkCfg _ ?model) _ =>
    try (replace (exit_code 2) with (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) by (apply bv_eq; reflexivity));
    apply u1_exit_u_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar TIDV)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENVC] in Ktid;
    let Hsp := fresh "Hsp2" in
    assert (Hsp : getr _ 2 = Z_to_bv 64 (bv_unsigned sp0 - OFF))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVC];
          rewrite P0; f_equal; lia);
    constructor;
    [ rewrite Hsp; rewrite u_small by lia; lia
    | rewrite Hsp; rewrite u_small by lia; apply mod16_sub;
      [ first [assumption | match goal with H : valid_sp _ |- _ => exact (proj2 (proj2 H)) end] | reflexivity]
    | rewrite Hsp; rewrite u_small by lia; unfold EXIT_STACK; change (Z.to_nat 1024) with 1024%nat;
      let Hst := fresh "Hst" in
      pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (- OFF - 1024)%Z 1024) in exact i)
                    _ _ _ (- OFF - 1024)%Z 1024 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
      unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVC] in Hst; rewrite P0 in Hst;
      match type of Hst with store_ok _ _ (Z_to_bv 64 ?x) _ = true =>
        replace (bv_unsigned sp0 - OFF - 1024)%Z with x by lia end;
      exact Hst
    | regv HR (4 : reg); reflexivity
    | regv HR (10 : reg); reflexivity
    | exists (bv_unsigned (ev E TIDV)); cbn [ev ENVC] in Ktid |- *; split;
      [ lia
      | let Htc := fresh "Htc" in
        krdF HK 0x102370%Z 4%nat Htc; rewrite Htc; cbn [ev ENVC];
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity ]
    | krd_solveF HK | krd_solveF HK
    | unfold cxx_cells_ok, cells_ok; apply (cells_of_kn _ _ _ _ _ HK); vm_compute; reflexivity
    | unfold exit_clear_common, exit_clear_u; cbn [app]; repeat apply Forall_cons; try apply Forall_nil;
      cbn [fst snd]; kimg_clear_solve HK
    | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK
    | first [exact Hh | reflexivity | assumption] | first [exact Hlazy | reflexivity | assumption] ]
  end end.

Ltac close_exit_u_core HR HK P0 Hh Hlazy sp0 OFF ENVC := close_exit_u_core_t 5%nat HR HK P0 Hh Hlazy sp0 OFF ENVC.

Ltac close_exit_u_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC :=
  lazymatch goal with
  | |- srealizes _ _ (t_emit _ _) =>
      cbn [W map]; eapply srz_conseq; [ close_exit_u_core_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC | apply t_emit_nil_exit ]
  | |- _ => close_exit_u_core_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC
  end.
Ltac close_exit_u HR HK P0 Hh Hlazy sp0 OFF ENVC := close_exit_u_t 5%nat HR HK P0 Hh Hlazy sp0 OFF ENVC.

Ltac close_exit_u1_core_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- srealizes _ (mkCfg _ ?model) _ =>
    try (replace (exit_code 2) with (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) by (apply bv_eq; reflexivity));
    apply u1_exit_u1_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar TIDV)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENVC] in Ktid;
    let Hsp := fresh "Hsp2" in
    assert (Hsp : getr _ 2 = Z_to_bv 64 (bv_unsigned sp0 - OFF))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVC];
          rewrite P0; f_equal; lia);
    constructor;
    [ rewrite Hsp; rewrite u_small by lia; lia
    | rewrite Hsp; rewrite u_small by lia; apply mod16_sub;
      [ first [assumption | match goal with H : valid_sp _ |- _ => exact (proj2 (proj2 H)) end] | reflexivity]
    | rewrite Hsp; rewrite u_small by lia; unfold EXIT_STACK; change (Z.to_nat 1024) with 1024%nat;
      let Hst := fresh "Hst" in
      pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (- OFF - 1024)%Z 1024) in exact i)
                    _ _ _ (- OFF - 1024)%Z 1024 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
      unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVC] in Hst; rewrite P0 in Hst;
      match type of Hst with store_ok _ _ (Z_to_bv 64 ?x) _ = true =>
        replace (bv_unsigned sp0 - OFF - 1024)%Z with x by lia end;
      exact Hst
    | regv HR (4 : reg); reflexivity
    | regv HR (10 : reg); reflexivity
    | exists (bv_unsigned (ev E TIDV)); cbn [ev ENVC] in Ktid |- *; split;
      [ lia
      | let Htc := fresh "Htc" in
        krdF HK 0x102370%Z 4%nat Htc; rewrite Htc; cbn [ev ENVC];
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity ]
    | krd_solveF HK | krd_solveF HK
    | unfold cxx_cells_ok, cells_ok; apply (cells_of_kn _ _ _ _ _ HK); vm_compute; reflexivity
    | unfold exit_clear_common, exit_clear_u1; cbn [app]; repeat apply Forall_cons; try apply Forall_nil;
      cbn [fst snd]; kimg_clear_solve HK
    | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK
    | first [exact Hh | reflexivity | assumption] | first [exact Hlazy | reflexivity | assumption] ]
  end end.

Ltac close_exit_t0_core_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- srealizes _ (mkCfg _ ?model) _ =>
    try (replace (exit_code 2) with (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) by (apply bv_eq; reflexivity));
    apply u1_exit_t0_Z;
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar TIDV)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENVC] in Ktid;
    let Hsp := fresh "Hsp2" in
    assert (Hsp : getr _ 2 = Z_to_bv 64 (bv_unsigned sp0 - OFF))
      by (regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVC];
          rewrite P0; f_equal; lia);
    constructor;
    [ rewrite Hsp; rewrite u_small by lia; lia
    | rewrite Hsp; rewrite u_small by lia; apply mod16_sub;
      [ first [assumption | match goal with H : valid_sp _ |- _ => exact (proj2 (proj2 H)) end] | reflexivity]
    | rewrite Hsp; rewrite u_small by lia; unfold EXIT_STACK; change (Z.to_nat 1024) with 1024%nat;
      let Hst := fresh "Hst" in
      pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (- OFF - 1024)%Z 1024) in exact i)
                    _ _ _ (- OFF - 1024)%Z 1024 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
      unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVC] in Hst; rewrite P0 in Hst;
      match type of Hst with store_ok _ _ (Z_to_bv 64 ?x) _ = true =>
        replace (bv_unsigned sp0 - OFF - 1024)%Z with x by lia end;
      exact Hst
    | regv HR (4 : reg); reflexivity
    | regv HR (10 : reg); reflexivity
    | exists (bv_unsigned (ev E TIDV)); cbn [ev ENVC] in Ktid |- *; split;
      [ lia
      | let Htc := fresh "Htc" in
        krdF HK 0x102370%Z 4%nat Htc; rewrite Htc; cbn [ev ENVC];
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity ]
    | krd_solveF HK | krd_solveF HK
    | unfold cxx_cells_ok, cells_ok; apply (cells_of_kn _ _ _ _ _ HK); vm_compute; reflexivity
    | unfold exit_clear_common, exit_clear_t0; cbn [app]; repeat apply Forall_cons; try apply Forall_nil;
      cbn [fst snd]; kimg_clear_solve HK
    | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK | krd_solveF HK
    | first [exact Hh | reflexivity | assumption] | first [exact Hlazy | reflexivity | assumption] ]
  end end.

Ltac close_exit_t0_core HR HK P0 Hh Hlazy sp0 OFF ENVC := close_exit_t0_core_t 5%nat HR HK P0 Hh Hlazy sp0 OFF ENVC.
Ltac close_exit_t0_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC :=
  lazymatch goal with
  | |- srealizes _ _ (t_emit _ _) =>
      cbn [W map]; eapply srz_conseq; [ close_exit_t0_core_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC | apply t_emit_nil_exit ]
  | |- _ => close_exit_t0_core_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC
  end.
Ltac close_exit_t0 HR HK P0 Hh Hlazy sp0 OFF ENVC := close_exit_t0_t 5%nat HR HK P0 Hh Hlazy sp0 OFF ENVC.

Ltac close_exit_u1_core HR HK P0 Hh Hlazy sp0 OFF ENVC := close_exit_u1_core_t 5%nat HR HK P0 Hh Hlazy sp0 OFF ENVC.

Ltac close_exit_u1_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC :=
  lazymatch goal with
  | |- srealizes _ _ (t_emit _ _) =>
      cbn [W map]; eapply srz_conseq; [ close_exit_u1_core_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC | apply t_emit_nil_exit ]
  | |- _ => close_exit_u1_core_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC
  end.
Ltac close_exit_u1 HR HK P0 Hh Hlazy sp0 OFF ENVC := close_exit_u1_t 5%nat HR HK P0 Hh Hlazy sp0 OFF ENVC.

Ltac close_exit_any_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC :=
  first [ solve [close_exit_u_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC] | solve [close_exit_u1_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC]
        | solve [close_exit_t0_t TIDV HR HK P0 Hh Hlazy sp0 OFF ENVC] ].
Ltac close_exit_any HR HK P0 Hh Hlazy sp0 OFF ENVC := close_exit_any_t 5%nat HR HK P0 Hh Hlazy sp0 OFF ENVC.
