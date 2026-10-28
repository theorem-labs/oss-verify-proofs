(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux RefPrintfLib LibTail RefMemcpyLib.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import RefExitBase AsScLib AsPrintfFirst.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SymExecCache.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition ABUF : Z := 0xc027a8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition apb_cells (w : Z) : list (Z * nat * Z) :=
  [(0x5ea8d8, 8%nat, 0x568878); (0x5ea8e0, 8%nat, 0x56571c); (0x5eaa68, 8%nat, 0x5699dc); (0x5eaa70, 8%nat, 0x569e10);
   (0x6aa8f8, 8%nat, 0x7fff8000); (0x6ab5d8, 1%nat, 1); (0x6ab5d9, 1%nat, 1); (0x73c47c, 1%nat, 1);
   (0x5ede88, 4%nat, 5);          (* [comment removed for export] *)
   (0x5edea8, 8%nat, 0xc02ba8);   (* [comment removed for export] *)
   (0x5edeb0, 8%nat, w);          (* [comment removed for export] *)
   (0x5edee8, 8%nat, 1024);       (* [comment removed for export] *)
   (0x5edf14, 4%nat, 0xffffffff); (* [comment removed for export] *)
   (0x5edf18, 4%nat, 0xffffffff); (* [comment removed for export] *)
   (0x7fffbb20, 8%nat, 0); (0x801784f0, 8%nat, 0)]%Z.

Record apbH (mem : word -> option byte) (sp : word) (w can : Z) : Prop := APBH {
  Psp16  : bv_unsigned sp mod 16 = 0;
  PspLo  : ASP_LO <= bv_unsigned sp;
  PspHi  : bv_unsigned sp <= ASP_HI;
  Pstk   : stk_ok RSEGS mem sp 3400;
  Pimg   : forall i, 0x10000 <= i < 0x195000 -> mem (Z_to_bv 64 i) = None;
  Pgot   : forall i, 0x571000 <= i < 0x5ea000 -> mem (Z_to_bv 64 i) = None;
  Pcells : cells_ok mem (apb_cells w);
  Pcan   : rdn RSEGS mem (Z_to_bv 64 0xc01cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  Pcan64 : 0 <= can < 2 ^ 64;
  Psh0   : forall a, 2147450880 + (bv_unsigned sp - 4096) / 8 <= a < 2147450880 + bv_unsigned sp / 8 ->
             mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0) }.

Definition apb_post (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w : Z) : Prop :=
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x1ef184) mem rom) (mkst regs' (Z_to_bv 64 0x1ef0d8) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 3400), 3400); (Z_to_bv 64 0x5ede88, 4);
                          (Z_to_bv 64 0x5edeb0, 8); (Z_to_bv 64 w, 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0x5edeb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0x5ede88) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition apb_kn (w : Z) : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI;
   KWr (SA (EVar 0) (-3400)) 3400;
   KImg 0x10000 0x195000; KImg 0x571000 0x5ea000;
   KWord (SA (ELit 0) 0xc01cd0) 8 (EVar 1);
   KWr (SA (ELit 0) 0x5ede88) 232; KWr (SA (ELit 0) 0xc027a8) 1024;
   KRange ap1_shx ASH_LO ASH_HI; KZero (SA ap1_shx 0) (ELit 8)]%Z
  ++ kn_cells (apb_cells w).

Definition apb_regions (w : Z) : list sregion :=
  [(SA (EVar 0) (-3400), 3400); (SA (ELit 0) 0x5ede88, 4); (SA (ELit 0) 0x5edeb0, 8); (SA (ELit 0) w, 2)].

Definition apb_run (w : Z) :=
  sym_exec RSEGS FUEL1 true STOPS1 scrA (SS 0x1ef184 ap1_sr [] (apb_kn w) 34) [].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma apb_run_unf : forall w, apb_run w = sym_exec RSEGS FUEL1 true STOPS1 scrA (SS 0x1ef184 ap1_sr [] (apb_kn w) 34) [].
Proof. intro w. exact_no_check (@eq_refl _ (sym_exec RSEGS FUEL1 true STOPS1 scrA (SS 0x1ef184 ap1_sr [] (apb_kn w) 34) [])). Qed.

Section Package.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : apbH mem sp w can.
  Hypothesis Hw : 0xc027a8 <= w <= 0xc027ac.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x1ef0d8.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := ENV (p1_vals regs sp can).

  Lemma adenot_lit0 : forall k, 0 <= k < 2 ^ 64 -> adenot E (SA (ELit 0) k) = Z_to_bv 64 k.
  Proof.
    intros k Hk. unfold adenot. cbn [a_base a_off edenot]. unfold v_addi.
    rewrite u64_lit by lia. f_equal; lia.
  Qed.

  Lemma apb_regs_ok : regs_ok E ap1_sr regs.
  Proof.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth ap1_sr allregs32 edenot].
    1: apply getr_zero.
    1: exact R1.
    1: exact R2.
    9: exact R11.
    all: unfold E; rewrite p1_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma apb_know_ok : know_ok RSEGS E mem (apb_kn w).
  Proof.
    destruct PH. pose proof (u64_range sp) as Hsp.
    assert (E0 : ev E 0 = sp) by reflexivity.
    assert (E1 : ev E 1 = Z_to_bv 64 can) by reflexivity.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0%Z) by reflexivity.
    pose proof (ap1_shx_denot E sp E0 PspLo0 PspHi0) as SHX.
    pose proof (ap1_shw_range (bv_unsigned sp) (conj PspLo0 PspHi0)) as (SR1 & SR2 & SR3).
    unfold ASP_LO, ASP_HI, ASH_LO, ASH_HI in *.
    unfold apb_kn. apply (proj2 (know_ok_app RSEGS _ _ _ _)). split.
    2:{ apply cells_know; [| assumption]. unfold apb_cells, cell_wf_b. cbn -[Z.leb Z.add].
        repeat (rewrite (proj2 (Z.leb_le _ _)) by lia). reflexivity. }
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. unfold ASP_LO, ASP_HI. lia.
    - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp 3400); [exact E0 | assumption | lia].
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | assumption].
    - eapply (kword_intro RSEGS _ mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | exact E1 | lia | lia | rewrite Z0; lia
        | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; assumption].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
      split; [lia|]. intros d m Hd Hm. apply store_ok_data. rewrite u64_lit by lia. lia.
    - apply krange_intro. rewrite SHX. unfold ASH_LO, ASH_HI. lia.
    - eapply (kzero_intro RSEGS _ mem ap1_shx (edenot E ap1_shx) 0 (ELit 8) 8);
        [reflexivity | reflexivity | rewrite SHX; lia | lia | rewrite SHX; lia |].
      intros i Hi. rewrite SHX. apply Psh1. lia.
  Qed.

  Lemma apb_case : forall ss' scs scr' kn' hs',
    apb_run w = (ss', scs, scr') ->
    s_pc ss' = 0x1ef0d8 ->
    log_covered (apb_regions w) (s_log ss') = true ->
    same_regs ap1_sr (s_regs ss') callee_saved = true ->
    carry (s_log ss') (apb_kn w) [] = (kn', [], hs') ->
    kread RSEGS kn' (ELit 0) 0x5edeb0 8 = Some (ELit (w + 2)) ->
    kread RSEGS kn' (ELit 0) 0x5ede88 4 = Some (ELit 5) ->
    kread RSEGS kn' (ELit 0) w 1 = Some (ELit 48) ->
    kread RSEGS kn' (ELit 0) (w + 1) 1 = Some (ELit 10) ->
    scs = p1_scsA ->
    apb_post regs mem rom sp w.
  Proof.
    intros ss' scs scr' kn' hs' Hrun Hpc Hcov Hsame Hcarry K1 K2 K3 K4 Hscs.
    rewrite (apb_run_unf w) in Hrun.   (* [comment removed for export] *)
    pose proof apb_regs_ok as HR. pose proof apb_know_ok as HK.
    assert (Hsc : scs_denot RSEGS mem E scs).
    { rewrite Hscs. destruct PH. apply (ap1_scs_ok (p1_vals regs sp can) mem sp); [reflexivity | assumption | assumption]. }
    destruct (run_sound RSEGS FUEL1 STOPS1 scrA 0x1ef184 ap1_sr (apb_kn w) 34 ss' scs scr' E mem rom regs
                Hrun HR HK Hsc) as (R' & HR' & Hlf & Hms).
    rewrite Hpc in Hms.
    assert (HK' : know_ok RSEGS E (mem_denot E mem (s_log ss')) kn').
    { eapply carry_after; [exact Hcarry | exact Hlf | exact HK | constructor]. }
    destruct PH. pose proof (u64_range sp) as Hsp. unfold ASP_LO, ASP_HI in *.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    exists R', (mem_denot E mem (s_log ss')).
    split; [exact Hms|]. split; [|split; [|split; [|split]]].
    - eapply (keeps_cs_of_same E); eassumption.
    - replace [(Z_to_bv 64 (bv_unsigned sp - 3400), 3400); (Z_to_bv 64 0x5ede88, 4);
               (Z_to_bv 64 0x5edeb0, 8); (Z_to_bv 64 w, 2)]
        with (map (rdenot E) (apb_regions w)).
      2:{ unfold apb_regions, rdenot, estart. cbn [map fst snd a_base a_off edenot].
          change (ev E 0) with sp. rewrite Z0.
          repeat (f_equal; [try (f_equal; lia)..]). all: f_equal; lia. }
      apply log_covered_frame; [exact Hcov | | exact Hlf].
      intros r Hr. unfold apb_regions in Hr. cbn [In] in Hr.
      unfold flat, estart.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd a_base a_off edenot];
        try change (ev E 0) with sp; rewrite ?Z0; lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) w 1 _ HK' K3 ltac:(lia) ltac:(lia)) as B0.
      pose proof (kread_rdn RSEGS E _ kn' (ELit 0) (w + 1) 1 _ HK' K4 ltac:(lia) ltac:(lia)) as B1.
      rewrite adenot_lit0 in B0, B1 by lia. cbn [edenot] in B0, B1.
      apply rdn_2.
      + rewrite u64_lit by lia. lia.
      + apply B0. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
      + rewrite u64_lit by lia. apply B1. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0x5edeb0 8 _ HK' K1 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
    - pose proof (kread_rdn RSEGS E _ kn' (ELit 0) 0x5ede88 4 _ HK' K2 ltac:(lia) ltac:(lia)) as B.
      rewrite adenot_lit0 in B by lia. cbn [edenot] in B.
      apply B. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0. lia.
  Qed.
End Package.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition resP0 := Eval vm_compute in (sym_exec_f RSEGS (tab_fun RSEGS p1_tab) FUEL1 true STOPS1 scrA (SS 0x1ef184 ap1_sr [] (apb_kn 0xc027a8) 34) []).   (* [comment removed for export] *)
Definition carP0 := Eval vm_compute in (carry (s_log (fst (fst resP0))) (apb_kn 0xc027a8) []).
Definition resP1 := Eval vm_compute in (sym_exec_f RSEGS (tab_fun RSEGS p1_tab) FUEL1 true STOPS1 scrA (SS 0x1ef184 ap1_sr [] (apb_kn 0xc027aa) 34) []).   (* [comment removed for export] *)
Definition carP1 := Eval vm_compute in (carry (s_log (fst (fst resP1))) (apb_kn 0xc027aa) []).
Definition resP2 := Eval vm_compute in (sym_exec_f RSEGS (tab_fun RSEGS p1_tab) FUEL1 true STOPS1 scrA (SS 0x1ef184 ap1_sr [] (apb_kn 0xc027ac) 34) []).   (* [comment removed for export] *)
Definition carP2 := Eval vm_compute in (carry (s_log (fst (fst resP2))) (apb_kn 0xc027ac) []).

Ltac run_case res car :=
  lazymatch goal with
  | PH : apbH ?mem ?sp ?w ?can, Hw : _, R1 : getr ?regs 1 = _, R2 : getr _ 2 = _, R11 : getr _ 11 = _ |- apb_post _ _ ?rom _ _ =>
      eapply (apb_case regs mem rom sp w can PH Hw R1 R2 R11
                (fst (fst res)) (snd (fst res)) (snd res) (fst (fst car)) (snd car));
      [ refine (eq_trans (apb_run_unf _) (eq_trans (p1_cached _ _ _ _ _ _) _)); vm_cast_no_check (@eq_refl _ res)   (* [comment removed for export] *)
      | reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_cast_no_check (@eq_refl _ car)
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity ]
  end.

Lemma apb_case0 : forall regs mem rom sp can,
  apbH mem sp 0xc027a8 can ->
  getr regs 1 = Z_to_bv 64 0x1ef0d8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  apb_post regs mem rom sp 0xc027a8.
Proof. intros regs mem rom sp can PH R1 R2 R11. assert (Hw : 0xc027a8 <= 0xc027a8 <= 0xc027ac) by lia. run_case resP0 carP0. Qed.

Lemma apb_case1 : forall regs mem rom sp can,
  apbH mem sp 0xc027aa can ->
  getr regs 1 = Z_to_bv 64 0x1ef0d8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  apb_post regs mem rom sp 0xc027aa.
Proof. intros regs mem rom sp can PH R1 R2 R11. assert (Hw : 0xc027a8 <= 0xc027aa <= 0xc027ac) by lia. run_case resP1 carP1. Qed.

Lemma apb_case2 : forall regs mem rom sp can,
  apbH mem sp 0xc027ac can ->
  getr regs 1 = Z_to_bv 64 0x1ef0d8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  apb_post regs mem rom sp 0xc027ac.
Proof. intros regs mem rom sp can PH R1 R2 R11. assert (Hw : 0xc027a8 <= 0xc027ac <= 0xc027ac) by lia. run_case resP2 carP2. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem aprintf0_buffered : forall (j : nat) regs mem rom (sp : word) (can : Z),
  (j <= 2)%nat ->
  apbH mem sp (ABUF + 2 * Z.of_nat j) can ->
  getr regs 1 = Z_to_bv 64 0x1ef0d8 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
  exists regs' mem',
    msteps RSEGS (mkst regs (Z_to_bv 64 0x1ef184) mem rom) (mkst regs' (Z_to_bv 64 0x1ef0d8) mem' rom)
    /\ keeps_cs regs regs'
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 3400), 3400); (Z_to_bv 64 0x5ede88, 4);
                          (Z_to_bv 64 0x5edeb0, 8); (Z_to_bv 64 (ABUF + 2 * Z.of_nat j), 2)]
    /\ rdn RSEGS mem' (Z_to_bv 64 (ABUF + 2 * Z.of_nat j)) 2 = Some [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]
    /\ rdn RSEGS mem' (Z_to_bv 64 0x5edeb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (ABUF + 2 * Z.of_nat j + 2)))
    /\ rdn RSEGS mem' (Z_to_bv 64 0x5ede88) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)).
Proof.
  intros j regs mem rom sp can Hj PH R1 R2 R11. unfold ABUF in *.
  destruct j as [|[|[|j]]]; [ | | | lia].
  - change (0xc027a8 + 2 * Z.of_nat 0) with 0xc027a8 in *. exact (apb_case0 regs mem rom sp can PH R1 R2 R11).
  - change (0xc027a8 + 2 * Z.of_nat 1) with 0xc027aa in *. exact (apb_case1 regs mem rom sp can PH R1 R2 R11).
  - change (0xc027a8 + 2 * Z.of_nat 2) with 0xc027ac in *. exact (apb_case2 regs mem rom sp can PH R1 R2 R11).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
