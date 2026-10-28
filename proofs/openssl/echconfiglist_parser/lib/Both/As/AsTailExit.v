(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail Spec
  LazyRestrict LazySR LazyFdNodes LazySym.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib
  AsPrintfFirst AsExitCas AsExitDefs AsExit.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section TailExit.
  Variables (L S Zr : list (word * word)).

  Record exitH (mem : word -> option byte) (sp : word) (tid : Z) (ro wpw : word) : Prop := EXH {
    Etid  : (0 < tid < 2147483648)%Z;
    Etidc : rdn RSEGS mem (Z_to_bv 64 0xbe1be8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
    Euse2 : forall i, (0x5edd90 <= i < 0x5ede88)%Z -> mem (Z_to_bv 64 i) = None;
    Eglb  : forall i, (0x5edf70 <= i < 0x6a7220 /\ ~ (0x5edf88 <= i < 0x5edf90))%Z -> mem (Z_to_bv 64 i) = None;   (* [comment removed for export] *)
    Eor1  : rdn RSEGS mem (Z_to_bv 64 0x5ede90) 8 = Some (word_to_le_bytes 8 ro);
    Eor2  : rdn RSEGS mem (Z_to_bv 64 0x5ede98) 8 = Some (word_to_le_bytes 8 ro);
    Eow1  : rdn RSEGS mem (Z_to_bv 64 0x5edeb0) 8 = Some (word_to_le_bytes 8 wpw);
    Eow2  : rdn RSEGS mem (Z_to_bv 64 0x5edec0) 8 = Some (word_to_le_bytes 8 wpw);
    Ecells : cells_ok mem ax_lit_cells;
    Eatexit : cells_ok mem (ax_atexit_cells false);                 (* [comment removed for export] *)
    Ebi   : rdn RSEGS mem (Z_to_bv 64 0xbdd420) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0));   (* [comment removed for export] *)
    Etext : forall i, (0x195000 <= i < 0x571000)%Z -> mem (Z_to_bv 64 i) = None;                 (* [comment removed for export] *)
    Eshw  : forall (a : word) (n : nat), (0x7fffa000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x7fffa000 + 0x17e800)%Z ->
              store_ok RSEGS mem a n = true }.

  (* [comment removed for export] *)
  Definition tail_regions (sp : word) (FR : Z) : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp - FR), FR); (Z_to_bv 64 0x5edca8, 232%Z)].

  Lemma outside_tail : forall (sp : word) FR x,
    (ASP_LO <= bv_unsigned sp)%Z -> (400 <= FR <= 8388608)%Z -> (0 <= x)%Z ->
    (x + 1 <= 0x5edca8 \/ 0x5edd90 <= x)%Z -> (x < 0x7fff00000000)%Z ->
    outside (Z_to_bv 64 x) (tail_regions sp FR).
  Proof.
    intros sp FR x Hlo HFR Hx H1 H2. unfold ASP_LO in Hlo. pose proof (u64_range sp).
    unfold tail_regions. cbn [outside]. unfold in_rng. rewrite !u64_lit by lia. lia.
  Qed.

  Lemma rdn_tail : forall mem mem' (sp : word) FR a n v,
    frame_mod mem mem' (tail_regions sp FR) ->
    (ASP_LO <= bv_unsigned sp)%Z -> (400 <= FR <= 8388608)%Z -> (0 <= a)%Z ->
    (a + Z.of_nat n <= 0x5edca8 \/ 0x5edd90 <= a)%Z -> (a + Z.of_nat n < 0x7fff00000000)%Z ->
    rdn RSEGS mem (Z_to_bv 64 a) n = v -> rdn RSEGS mem' (Z_to_bv 64 a) n = v.
  Proof.
    intros mem mem' sp FR a n v FM Hlo HFR Ha H1 H2 Hr. rewrite <- Hr.
    apply (frame_mod_rdn RSEGS mem mem' _ n (Z_to_bv 64 a) FM); rewrite u64_lit by lia; [|lia].
    intros i Hi. apply outside_tail; try assumption; lia.
  Qed.

  Lemma none_tail : forall mem mem' (sp : word) FR lo hi,
    frame_mod mem mem' (tail_regions sp FR) ->
    (ASP_LO <= bv_unsigned sp)%Z -> (400 <= FR <= 8388608)%Z -> (0 <= lo)%Z ->
    (hi <= 0x5edca8 \/ 0x5edd90 <= lo)%Z -> (hi < 0x7fff00000000)%Z ->
    (forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
    forall i, (lo <= i < hi)%Z -> mem' (Z_to_bv 64 i) = None.
  Proof.
    intros mem mem' sp FR lo hi FM Hlo HFR H0 H1 H2 Hn i Hi.
    rewrite (frame_mod_byte mem mem' _ (Z_to_bv 64 i) FM); [apply Hn; exact Hi|].
    apply outside_tail; try assumption; lia.
  Qed.

  Lemma cells_tail : forall mem mem' (sp : word) FR cs,
    frame_mod mem mem' (tail_regions sp FR) ->
    (ASP_LO <= bv_unsigned sp)%Z -> (400 <= FR <= 8388608)%Z ->
    Forall (fun c => match c with (a, w, _) =>
      (0 <= a)%Z /\ (a + Z.of_nat w <= 0x5edca8 \/ 0x5edd90 <= a)%Z /\ (a + Z.of_nat w < 0x7fff00000000)%Z end) cs ->
    cells_ok mem cs -> cells_ok mem' cs.
  Proof.
    intros mem mem' sp FR cs FM Hlo HFR Hcs Hc. unfold cells_ok in *.
    induction cs as [|[[a w] v] cs IH]; [constructor|].
    inversion Hcs as [|c cs' Hc1 Hcs']; subst. inversion Hc as [|c cs'' Hok Hc']; subst.
    constructor; [| apply IH; assumption].
    unfold cell_ok in *. destruct Hc1 as (A1 & A2 & A3).
    apply (rdn_tail mem mem' sp FR a w _ FM Hlo HFR A1 A2 A3 Hok).
  Qed.

  (* [comment removed for export] *)
  Lemma ax_lit_cells_split :
    ax_lit_cells = (firstn 13 ax_lit_cells ++ [(0x5edd34, 4%nat, 0xffffffff)] ++ skipn 14 ax_lit_cells)%Z.   (* [comment removed for export] *)
  Proof. reflexivity. Qed.

  Lemma ax_lit_cells_apart :
    Forall (fun c : Z * nat * Z => match c with (a, w, _) =>
      (0 <= a)%Z /\ (a + Z.of_nat w <= 0x5edca8 \/ 0x5edd90 <= a)%Z /\ (a + Z.of_nat w < 0x7fff00000000)%Z end)
      (firstn 13 ax_lit_cells ++ skipn 14 ax_lit_cells).
  Proof. cbn. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

  Lemma ax_atexit1_apart :
    Forall (fun c : Z * nat * Z => match c with (a, w, _) =>
      (0 <= a)%Z /\ (a + Z.of_nat w <= 0x5edca8 \/ 0x5edd90 <= a)%Z /\ (a + Z.of_nat w < 0x7fff00000000)%Z end)
      (ax_atexit_cells false).
  Proof. cbn. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

  Theorem tail_exit2 : forall regs mem mem' msF mo (sp : word) (FR tid can : Z) (ro wpw we re : word),
    exitH mem sp tid ro wpw ->
    (bv_unsigned sp mod 16 = 0)%Z -> (ASP_LO <= bv_unsigned sp)%Z -> (bv_unsigned sp <= ASP_HI)%Z ->
    (forall i, (0x10000 <= i < 0x195000)%Z -> mem (Z_to_bv 64 i) = None) ->
    (forall i, (0x571000 <= i < 0x5ea000)%Z -> mem (Z_to_bv 64 i) = None) ->
    frame_mod mem mem' (tail_regions sp FR) -> (400 <= FR <= 8388608)%Z ->
    stk_ok RSEGS mem' sp 1024 ->                                                  (* [comment removed for export] *)
    (0 <= can < 2 ^ 64)%Z -> rdn RSEGS mem' (Z_to_bv 64 0xc01cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can)) ->
    rdn RSEGS mem' (Z_to_bv 64 0x5edcd0) 8 = Some (word_to_le_bytes 8 we) ->
    rdn RSEGS mem' (Z_to_bv 64 0x5edce0) 8 = Some (word_to_le_bytes 8 we) ->
    rdn RSEGS mem' (Z_to_bv 64 0x5edcb0) 8 = Some (word_to_le_bytes 8 re) ->
    rdn RSEGS mem' (Z_to_bv 64 0x5edcb8) 8 = Some (word_to_le_bytes 8 re) ->
    rdn RSEGS mem' (Z_to_bv 64 0x5edd34) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ->
    getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0xbe1c90 -> getr regs 10 = Z_to_bv 64 2 ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 AEXIT) mem' (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (exit_code 2) (m_fs mo)).
  Proof.
    intros regs mem mem' msF mo sp FR tid can ro wpw we re XH Hal Hlo Hhi Himg Hgot FM HFR Hstk Hcan64 Hcan
           Hwe1 Hwe2 Hre1 Hre2 Hlock R2 R4 R10 OK RS.
    destruct XH.
    replace (exit_code 2) with (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) by (apply bv_eq; reflexivity).
    apply (as_exit_clean1 L S Zr regs mem' msF mo sp (Z_to_bv 64 2) we re ro wpw tid can); try assumption.
    - split; try assumption.
      + apply (rdn_tail mem mem' sp FR 0xbe1be8 4 _ FM Hlo HFR); [lia | lia | lia | exact Etidc0].
      + apply (none_tail mem mem' sp FR 0x10000 0x195000 FM Hlo HFR); [lia | lia | lia | exact Himg].
      + apply (none_tail mem mem' sp FR 0x195000 0x571000 FM Hlo HFR); [lia | lia | lia | exact Etext0].
      + apply (none_tail mem mem' sp FR 0x571000 0x5ea000 FM Hlo HFR); [lia | lia | lia | exact Hgot].
      + apply (none_tail mem mem' sp FR 0x5edd90 0x5ede88 FM Hlo HFR); [lia | lia | lia | exact Euse3].
      + intros i [Hi Hn]. destruct (Z.lt_ge_cases i 0x5edf88) as [Hc|Hc].
        * apply (none_tail mem mem' sp FR 0x5edf70 0x5edf88 FM Hlo HFR); [lia | lia | lia | intros j Hj; apply Eglb0; lia | lia].
        * apply (none_tail mem mem' sp FR 0x5edf90 0x6a7220 FM Hlo HFR); [lia | lia | lia | intros j Hj; apply Eglb0; lia | lia].
      + apply (rdn_tail mem mem' sp FR 0x5ede90 8 _ FM Hlo HFR); [lia | lia | lia | exact Eor3].
      + apply (rdn_tail mem mem' sp FR 0x5ede98 8 _ FM Hlo HFR); [lia | lia | lia | exact Eor4].
      + rewrite ax_lit_cells_split in Ecells0 |- *. unfold cells_ok in *.
        apply Forall_app in Ecells0 as [C1 C23]. apply Forall_app in C23 as [_ C3].
        pose proof (cells_tail mem mem' sp FR _ FM Hlo HFR ax_lit_cells_apart) as CT. unfold cells_ok in CT.
        assert (C13 : Forall (cell_ok mem) (firstn 13 ax_lit_cells ++ skipn 14 ax_lit_cells)) by (apply Forall_app; split; assumption).
        apply CT in C13. apply Forall_app in C13 as [C1' C3'].
        apply Forall_app; split; [exact C1'|]. constructor; [exact Hlock | exact C3'].
      + exact (cells_tail mem mem' sp FR _ FM Hlo HFR ax_atexit1_apart Eatexit0).
      + intros a n Ha Hn. eapply frame_mod_store_ok; [exact FM|]. apply Eshw0; assumption.
    - apply (rdn_tail mem mem' sp FR 0xbdd420 1 _ FM Hlo HFR); [lia | lia | lia | exact Ebi0].
    - apply (rdn_tail mem mem' sp FR 0x5edeb0 8 _ FM Hlo HFR); [lia | lia | lia | exact Eow3].
    - apply (rdn_tail mem mem' sp FR 0x5edec0 8 _ FM Hlo HFR); [lia | lia | lia | exact Eow4].
  Qed.
End TailExit.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
