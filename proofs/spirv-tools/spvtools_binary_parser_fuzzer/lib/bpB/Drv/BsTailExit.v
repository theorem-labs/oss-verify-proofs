(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatSim BSeqExec BStoreOk BShapeAlg BAgentLib BFrame BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSpec BazyRestrict BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BRefExitBase BsPrintfFirst BsExitDefs DvB_ExitPre DvB_ExitPreT DvB_ExitIface.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition xk_stderr : list (Z * nat * Z) :=
  [(0x189920, 4%nat, 0x5); (0x189940, 8%nat, 0x0); (0x189978, 8%nat, 0x6e6070); (0x189980, 8%nat, 0x0);
   (0x1899a8, 4%nat, 0xffffffff); (0x1899ac, 4%nat, 0xffffffff); (0x1899b0, 4%nat, 0xffffffff)]%Z.
Definition xk_rest : list (Z * nat * Z) :=
  Eval vm_compute in List.filter (fun c => match c with (a, _, _) => negb ((0x189920 <=? a) && (a <? 0x189a08))%Z end) xk_common.

Definition xk_Uout : list (Z * nat * Z) := [(0x6e58b0, 4%nat, 0x3); (0x189b20, 8%nat, 0x0); (0x189b88, 4%nat, 0x0); (0x189b90, 4%nat, 0xa)]%Z.

Definition cell_eqb (c d : Z * nat * Z) : bool :=
  match c, d with (a, w, v), (a', w', v') => (Z.eqb a a' && Nat.eqb w w' && Z.eqb v v')%bool end.
Definition cells_incl_b (c1 c2 : list (Z * nat * Z)) : bool := forallb (fun c => existsb (cell_eqb c) c2) c1.

Lemma cells_ok_incl_b : forall m c1 c2, cells_incl_b c1 c2 = true -> cells_ok m c2 -> cells_ok m c1.
Proof.
  intros m c1 c2 H H2. unfold cells_ok in *. apply Forall_forall. intros c Hc.
  pose proof (proj1 (forallb_forall _ _) H c Hc) as Hx. apply existsb_exists in Hx as (d & Hd & Heq).
  destruct c as [[a w] v], d as [[a' w'] v']. cbn in Heq.
  apply andb_prop in Heq as [Heq H3]. apply andb_prop in Heq as [H1 H2'].
  apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2'. apply Z.eqb_eq in H3. subst.
  exact (proj1 (Forall_forall _ _) H2 _ Hd).
Qed.

Lemma xk_common_split : cells_incl_b xk_common (xk_stderr ++ xk_rest) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma xk_U_split : cells_incl_b xk_U (xk_stderr ++ xk_Uout) = true.
Proof. vm_compute. reflexivity. Qed.

Section TailExit.
  Variables (L S Zr : list (word * word)).

  Record exitA (mem : word -> option byte) (sp : word) (tid can TB : Z) : Prop := EXA {
    Atid  : (0 < tid < 2147483648)%Z;
    Atidc : rdn RSEGS mem (Z_to_bv 64 0x6c57b0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
    Aimg  : forall i, (0x10000 <= i < 0x91000)%Z -> mem (Z_to_bv 64 i) = None;
    Agot  : forall i, (0x17e000 <= i < 0x186000)%Z -> mem (Z_to_bv 64 i) = None;
    Ause2 : forall i, (0x189a08 <= i < 0x189b00)%Z -> mem (Z_to_bv 64 i) = None;
    Aglb  : forall i, (0x189be8 <= i < 0x18d980)%Z -> mem (Z_to_bv 64 i) = None;
    Acan  : rdn RSEGS mem (Z_to_bv 64 0x6e5898) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Acan64 : (0 <= can < 2 ^ 64)%Z;
    ATBc  : rdn RSEGS mem (Z_to_bv 64 0x190888) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 TB));
    ATBal : (TB mod 4096 = 0)%Z;
    ATBr  : (ATB_LO <= TB <= ATB_HI)%Z;
    ATBimg : (TB + 0x38e000 <= AIMGR_LO \/ AIMGR_LO + AIMGR_N <= TB)%Z;
    ATBsh  : (TB + 0x38e000 <= ASHR_LO \/ ASHR_LO + ASHR_N <= TB)%Z;
    ATBsp  : (TB + 0x38e000 + 4194304 <= bv_unsigned sp)%Z;
    AAHM  : forall i, (0 <= i < 96)%Z -> mem (Z_to_bv 64 (TB + 0x1e34f8 + i)) = Some (Z_to_bv 8 0)
                                        /\ mem (Z_to_bv 64 (TB + 0x2cf448 + i)) = Some (Z_to_bv 8 0);
    AAHMw : forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 8)%Z ->
              store_ok RSEGS mem (Z_to_bv 64 (TB + 0x1e34f8 + d)) m = true /\ store_ok RSEGS mem (Z_to_bv 64 (TB + 0x2cf448 + d)) m = true;
    AshM  : rdn RSEGS mem (Z_to_bv 64 0x800d0720) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    AshS  : forall a, (2147450880 + (bv_unsigned sp - 4096) / 8 <= a < 2147450880 + bv_unsigned sp / 8)%Z ->
              mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0);
    Ashw  : forall (a : word) (n : nat), (0x7fffa000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x7fffa000 + 0xdb000)%Z ->
              store_ok RSEGS mem a n = true;
    Acells : cells_ok mem xk_rest;
    Aout  : cells_ok mem xk_Uout }.

  Definition tail_regions (sp : word) (FR : Z) : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp - FR), FR); (Z_to_bv 64 0x189920, 232%Z)].

  Lemma outside_tail : forall (sp : word) FR x,
    (ASP_LO <= bv_unsigned sp)%Z -> (400 <= FR <= 8388608)%Z -> (0 <= x)%Z ->
    (x + 1 <= 0x189920 \/ 0x189a08 <= x)%Z -> (x < 0x7fff7e800000)%Z ->
    outside (Z_to_bv 64 x) (tail_regions sp FR).
  Proof.
    intros sp FR x Hlo HFR Hx H1 H2. unfold ASP_LO in Hlo. pose proof (u64_range sp).
    unfold tail_regions. cbn [outside]. unfold in_rng. rewrite !u64_lit by lia. lia.
  Qed.

  Lemma byte_tail_lo : forall mem mem' (sp : word) FR x v,
    frame_mod mem mem' (tail_regions sp FR) ->
    (400 <= FR <= 4194304)%Z -> (FR <= bv_unsigned sp)%Z -> (0 <= x)%Z ->
    (x + 1 <= 0x189920 \/ 0x189a08 <= x)%Z -> (x + 1 <= bv_unsigned sp - FR)%Z ->
    mem (Z_to_bv 64 x) = v -> mem' (Z_to_bv 64 x) = v.
  Proof.
    intros mem mem' sp FR x v FM HFR Hsp H0 H1 H2 Hx. rewrite (frame_mod_byte mem mem' _ (Z_to_bv 64 x) FM); [exact Hx|].
    pose proof (u64_range sp). unfold tail_regions. cbn [outside]. unfold in_rng. rewrite !u64_lit by lia. lia.
  Qed.

  Lemma rdn_tail : forall mem mem' (sp : word) FR a n v,
    frame_mod mem mem' (tail_regions sp FR) ->
    (ASP_LO <= bv_unsigned sp)%Z -> (400 <= FR <= 8388608)%Z -> (0 <= a)%Z ->
    (a + Z.of_nat n <= 0x189920 \/ 0x189a08 <= a)%Z -> (a + Z.of_nat n < 0x7fff00000000)%Z ->
    rdn RSEGS mem (Z_to_bv 64 a) n = v -> rdn RSEGS mem' (Z_to_bv 64 a) n = v.
  Proof.
    intros mem mem' sp FR a n v FM Hlo HFR Ha H1 H2 Hr. rewrite <- Hr.
    apply (frame_mod_rdn RSEGS mem mem' _ n (Z_to_bv 64 a) FM); rewrite u64_lit by lia; [|lia].
    intros i Hi. apply outside_tail; try assumption; lia.
  Qed.

  Lemma byte_tail : forall mem mem' (sp : word) FR x v,
    frame_mod mem mem' (tail_regions sp FR) ->
    (ASP_LO <= bv_unsigned sp)%Z -> (400 <= FR <= 8388608)%Z -> (0 <= x)%Z ->
    (x + 1 <= 0x189920 \/ 0x189a08 <= x)%Z -> (x < 0x7fff7e800000)%Z ->
    mem (Z_to_bv 64 x) = v -> mem' (Z_to_bv 64 x) = v.
  Proof.
    intros mem mem' sp FR x v FM Hlo HFR H0 H1 H2 Hx. rewrite (frame_mod_byte mem mem' _ (Z_to_bv 64 x) FM); [exact Hx|].
    apply outside_tail; assumption.
  Qed.

  Lemma cells_tail : forall mem mem' (sp : word) FR cs,
    frame_mod mem mem' (tail_regions sp FR) ->
    (ASP_LO <= bv_unsigned sp)%Z -> (400 <= FR <= 8388608)%Z ->
    Forall (fun c => match c with (a, w, _) =>
      (0 <= a)%Z /\ (a + Z.of_nat w <= 0x189920 \/ 0x189a08 <= a)%Z /\ (a + Z.of_nat w < 0x7fff00000000)%Z end) cs ->
    cells_ok mem cs -> cells_ok mem' cs.
  Proof.
    intros mem mem' sp FR cs FM Hlo HFR Hcs Hc. unfold cells_ok in *.
    induction cs as [|[[a w] v] cs IH]; [constructor|].
    inversion Hcs as [|c cs' Hc1 Hcs']; subst. inversion Hc as [|c cs'' Hok Hc']; subst.
    constructor; [| apply IH; assumption].
    unfold cell_ok in *. destruct Hc1 as (A1 & A2 & A3).
    apply (rdn_tail mem mem' sp FR a w _ FM Hlo HFR A1 A2 A3 Hok).
  Qed.

  Definition cell_apart_b (c : Z * nat * Z) : bool :=
    match c with (a, w, _) => ((0 <=? a) && ((a + Z.of_nat w <=? 0x189920) || (0x189a08 <=? a)) && (a + Z.of_nat w <? 0x7fff00000000))%Z end.
  Lemma cells_apart_of_b : forall cs, forallb cell_apart_b cs = true ->
    Forall (fun c => match c with (a, w, _) =>
      (0 <= a)%Z /\ (a + Z.of_nat w <= 0x189920 \/ 0x189a08 <= a)%Z /\ (a + Z.of_nat w < 0x7fff00000000)%Z end) cs.
  Proof.
    intros cs H. apply Forall_forall. intros [[a w] v] Hin. pose proof (proj1 (forallb_forall _ _) H _ Hin) as Hc.
    cbn in Hc. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H3. apply orb_prop in H2 as [H2|H2]; apply Z.leb_le in H2; lia.
  Qed.

  Theorem tail_exitA : forall regs mem mem' msF mo (sp : word) (FR tid can TB : Z),
    exitA mem sp tid can TB ->
    (bv_unsigned sp mod 16 = 0)%Z -> (ASP_LO <= bv_unsigned sp)%Z -> (bv_unsigned sp <= ASP_HI)%Z ->
    frame_mod mem mem' (tail_regions sp FR) -> (400 <= FR <= 4194304)%Z ->
    stk_ok RSEGS mem' sp 2560 ->
    cells_ok mem' xk_stderr ->
    getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0x6c5858 -> getr regs 10 = Z_to_bv 64 2 ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 AEXIT) mem' (seg_rom RSEGS) ->
    realizes RSEGS (mkCfg msF mo) (t_exit (exit_code 2) (m_fs mo)).
  Proof.
    intros regs mem mem' msF mo sp FR tid can TB XA Hal Hlo Hhi FM HFR Hstk Herr R2 R4 R10 OK RS.
    destruct XA. pose proof (u64_range sp) as Hsp.
    unfold ASP_LO, ASP_HI in *.
    replace (exit_code 2) with (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) by (apply bv_eq; reflexivity).
    assert (Hrest : cells_ok mem' xk_rest)
      by (apply (cells_tail mem mem' sp FR xk_rest FM ltac:(unfold ASP_LO; lia) ltac:(lia));
          [apply cells_apart_of_b; vm_compute; reflexivity | exact Acells0]).
    assert (Hout : cells_ok mem' xk_Uout)
      by (apply (cells_tail mem mem' sp FR xk_Uout FM ltac:(unfold ASP_LO; lia) ltac:(lia));
          [apply cells_apart_of_b; vm_compute; reflexivity | exact Aout0]).
    apply (as_exit_U regs mem' msF mo L S Zr sp (Z_to_bv 64 2) tid can TB); try assumption.
    - split; try assumption.
      + apply (rdn_tail mem mem' sp FR 0x6c57b0 4 _ FM ltac:(unfold ASP_LO; lia) ltac:(lia)); [lia | lia | lia | exact Atidc0].
      + intros i Hi. apply (byte_tail mem mem' sp FR i _ FM ltac:(unfold ASP_LO; lia) ltac:(lia)); [lia | lia | lia | apply Aimg0; exact Hi].
      + intros i Hi. apply (byte_tail mem mem' sp FR i _ FM ltac:(unfold ASP_LO; lia) ltac:(lia)); [lia | lia | lia | apply Agot0; exact Hi].
      + intros i Hi. apply (byte_tail mem mem' sp FR i _ FM ltac:(unfold ASP_LO; lia) ltac:(lia)); [lia | lia | lia | apply Ause3; exact Hi].
      + intros i Hi. apply (byte_tail mem mem' sp FR i _ FM ltac:(unfold ASP_LO; lia) ltac:(lia)); [lia | lia | lia | apply Aglb0; exact Hi].
      + apply (rdn_tail mem mem' sp FR 0x6e5898 8 _ FM ltac:(unfold ASP_LO; lia) ltac:(lia)); [lia | lia | lia | exact Acan0].
      + apply (rdn_tail mem mem' sp FR 0x190888 8 _ FM ltac:(unfold ASP_LO; lia) ltac:(lia)); [lia | lia | lia | exact ATBc0].
      + lia.
      + intros i Hi. destruct (AAHM0 i Hi) as [A1 A2]. split.
        * unfold ATB_LO, ATB_HI, AIMGR_LO, AIMGR_N in *.
          apply (byte_tail_lo mem mem' sp FR _ _ FM HFR); [lia | lia | lia | lia | exact A1].
        * unfold ATB_LO, ATB_HI, AIMGR_LO, AIMGR_N in *.
          apply (byte_tail_lo mem mem' sp FR _ _ FM HFR); [lia | lia | lia | lia | exact A2].
      + intros d m Hd Hm. destruct (AAHMw0 d m Hd Hm) as [W1 W2].
        split; eapply frame_mod_store_ok; eassumption.
      + apply (rdn_tail mem mem' sp FR 0x800d0720 8 _ FM ltac:(unfold ASP_LO; lia) ltac:(lia)); [lia | lia | lia | exact AshM0].
      + intros a Ha. apply (byte_tail mem mem' sp FR a _ FM ltac:(unfold ASP_LO; lia) ltac:(lia));
          [Z.div_mod_to_equations; lia | lia | Z.div_mod_to_equations; lia | apply AshS0; exact Ha].
      + intros a n Ha Hn. eapply frame_mod_store_ok; [exact FM|]. apply Ashw0; assumption.
      + apply (cells_ok_incl_b mem' xk_common (xk_stderr ++ xk_rest) xk_common_split).
        unfold cells_ok in *. apply Forall_app. split; assumption.
    - apply (cells_ok_incl_b mem' xk_U (xk_stderr ++ xk_Uout) xk_U_split).
      unfold cells_ok in *. apply Forall_app. split; assumption.
  Qed.
End TailExit.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
