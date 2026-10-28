(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BAmb BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BHoare BFrame BShapeLaws BpecConsts BMmapSim BAllocSim BFileSim BAgentLib BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BSymDriveH4 BLibKnowFrame BSymAux BSpec BLibTail BeapCeil BazyRestrict BazySR BainDefs BainArith BainWalk_defs BainSegs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BRefExitBase BsDrvRun BsTRWalk_defs.
Import ListNotations.
Import BPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition cT0b := Eval vm_compute in carryM rT0b knT0.
Definition cT1a := Eval vm_compute in carryM rT1a knT.
Definition cT1b := Eval vm_compute in carryM rT1b knT.
Definition cT1c := Eval vm_compute in carryM rT1c knT.
Definition cT1d := Eval vm_compute in carryM rT1d knT.
Definition cT2 := Eval vm_compute in carryM rT2 knT.
Definition cT3 := Eval vm_compute in carryM rT3 knT.
Definition cT4 := Eval vm_compute in carryM rT4 knT.
Definition cT5 := Eval vm_compute in carryM rT5 knT.
Definition cT6 := Eval vm_compute in carryM rT6 knT.
Definition cT7a := Eval vm_compute in carryM rT7a knT.
Definition cT7b := Eval vm_compute in carryM rT7b knT.
Definition cT8 := Eval vm_compute in carryM rT8 knT8.

Definition regT : list sregion := [(SA (EVar 0) (-80), 80)]%Z.
Definition regTf : list sregion := [(SA (ELit 0) AAEF, 1)]%Z.
Definition regT0 : list sregion :=
  [(SA (EVar 0) (-128), 128); (SA (ELit 0) AINIT, 1); (SA (ELit 0) AX_SLOT, 4); (SA (ELit 0) AX_F3, 8); (SA (ELit 0) AX_A3, 8)]%Z.
Definition regT_w (sp : word) : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 80), 80%Z)].
Definition regTf_w : list (word * Z) := [(Z_to_bv 64 AAEF, 1%Z)].
Definition regT0_w (sp : word) : list (word * Z) :=
  [(Z_to_bv 64 (bv_unsigned sp - 128), 128%Z); (Z_to_bv 64 AINIT, 1%Z); (Z_to_bv 64 AX_SLOT, 4%Z); (Z_to_bv 64 AX_F3, 8%Z); (Z_to_bv 64 AX_A3, 8%Z)].

Lemma covT0b : log_covered regT0 (s_log (fst (fst rT0b))) = true. Proof. vm_compute. reflexivity. Qed.

Lemma covT5 : log_covered regTf (s_log (fst (fst rT5))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma covT6 : log_covered regTf (s_log (fst (fst rT6))) = true. Proof. vm_compute. reflexivity. Qed.

Ltac run_segT stops scr pc sr kn nx r c E M R :=
  lazymatch goal with
  | HVx : BsIface.as_VIS ?Hh ?sx ?msFx = _, DLx : asan_driver_laws ?Hh |- @realizes _ _ (mkCfg ?msFx ?mox) _ =>
    eapply (drv_run_lf Hh DLx sx FUELM stops scr pc sr kn nx (fst (fst r)) (snd (fst r)) (snd r)
              (fst (fst c)) (snd (fst c)) (snd c) E M R msFx mox);
    [ vm_cast_no_check (@eq_refl _ r) | vm_cast_no_check (@eq_refl _ c) | | | | scs_nil | | | ]
  end.

Section BlocksT.
  Context {fx : DFP}.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.
  Variable sp : word.
  Hypothesis Hsp16 : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HspLo : (0x7fff7f811000 <= bv_unsigned sp)%Z.
  Hypothesis HspHi : (bv_unsigned sp <= 0x7fffffffff80)%Z.
  Let rom := seg_rom asegs.

  Definition aro_none (mem : word -> option byte) : Prop := forall i, (0x10000 <= i < 0x91000)%Z -> mem (Z_to_bv 64 i) = None.
  Definition arelro_none (mem : word -> option byte) : Prop := forall i, (0x17e000 <= i < 0x186000)%Z -> mem (Z_to_bv 64 i) = None.

  Definition latch_ok (mem : word -> option byte) : Prop := stk_ok RSEGS mem (Z_to_bv 64 (AINIT + 16)) 16.

  Definition atx_ok (mem : word -> option byte) : Prop := stk_ok RSEGS mem (Z_to_bv 64 (AX_FIN + 0x140)) 0x140.

  Definition TV (A cfg N D ib c r PL CP OW S3 : word) : mv :=
    MV sp A cfg N D ib c r PL CP OW S3 (Z_to_bv 64 0) (Z_to_bv 64 0).

  Ltac evs := cbn [edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1 TV].
  Ltac unset_v := repeat match goal with w := TV _ _ _ _ _ _ _ _ _ _ _ |- _ => subst w | w := MV _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => subst w end.
  Ltac fin_reg HR' r :=
    unset_v; regv HR' r; cbn [edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1 TV];
    first [ reflexivity | assumption
          | rewrite ev_junk by lia; first [assumption | symmetry; assumption | reflexivity]
          | ed_lin idtac; unorm; first [reflexivity | f_equal; lia | apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; f_equal; lia] ].

  Ltac sc_eqb :=
    rewrite ?eqb_ZZ by lia;
    first [ apply Z.eqb_eq; lia
          | apply Z.eqb_neq; lia
          | rewrite Bool.negb_true_iff; apply Z.eqb_neq; lia
          | reflexivity ].
  Ltac sc_open :=
    lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end;
    unset_v; repeat apply Forall_cons; try apply Forall_nil;
    cbn [sc_denot branch_taken edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1 TV]; ed_lin idtac; unorm.
  Ltac evs_in H := cbn [edenot ev MENV mvals vals_ev nth app v_sp0 v_tid v_pp v_A v_len v_cap v_A2 v_n v_b8 v_b9 v_b10 v_b11 v_b0 v_b1 TV] in H.

  Lemma knT_ok : forall v regs mem,
    v_sp0 v = sp ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem ->
    know_ok RSEGS (MENV v regs) mem knT.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs mem Ev Hstk Hro Hrel Hlatch. cbn in Ev. subst v0.
    unfold knT. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. evs. exact Hsp16.
    - apply krange_intro. evs. lia.
    - cbn [kentry_ok]. split; [apply flat_intro; evs; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. evs.
      pose proof (Hstk (Z_to_bv 64 (bv_unsigned sp + -128 + d)) m) as Hs.
      rewrite !u_small in Hs by lia. apply Hs; lia.
    - cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot a_base a_off]; unfold AINIT; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. unfold AINIT. rewrite (u_small 0) by lia.
      pose proof (Hlatch (Z_to_bv 64 (0 + 7091856 + d)) m) as Hs. unfold AINIT in Hs. rewrite !u_small in Hs by lia. apply Hs; lia.
    - apply kimg_intro; [lia|lia|exact Hro].
    - apply kimg_intro; [lia|lia|exact Hrel].
  Qed.

  Definition tcell (mem : word -> option byte) (c : Z * nat * Z) : Prop :=
    match c with (a, w, v) => rdn RSEGS mem (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)) end.
  Definition tcells (mem : word -> option byte) (cs : list (Z * nat * Z)) : Prop := Forall (tcell mem) cs.

  Lemma kword_cell : forall E mem (a : Z) (w : nat) (v : Z),
    (w <= 8)%nat -> (0 <= a)%Z -> (a + Z.of_nat w < 2 ^ 64)%Z -> tcell mem (a, w, v) ->
    kentry_ok RSEGS E mem (KWord (SA (ELit 0) a) w (ELit v)).
  Proof.
    intros E mem a w v Hw Ha Hn HC. cbn [kentry_ok a_base a_off edenot]. split; [exact Hw|].
    split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia; lia|].
    unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia. rewrite Z.add_0_l. exact HC.
  Qed.

  Lemma knT0_ok : forall v regs mem,
    v_sp0 v = sp ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem -> atx_ok mem -> tcells mem atx_cells0 ->
    know_ok RSEGS (MENV v regs) mem knT0.
  Proof.
    intros v regs mem Ev Hstk Hro Hrel Hlatch Hatx HC.
    change knT0 with (knT ++ [KWr (SA (ELit 0) AX_FIN) 0x140]%Z ++ kn_cells atx_cells0). unfold know_ok. rewrite !Forall_app.
    split; [apply knT_ok; assumption|]. split.
    - apply Forall_cons; [|apply Forall_nil].
      cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot a_base a_off]; unfold AX_FIN; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. unfold AX_FIN. rewrite (u_small 0) by lia.
      pose proof (Hatx (Z_to_bv 64 (0 + 7231656 + d)) m) as Hs. unfold AX_FIN in Hs. rewrite !u_small in Hs by lia. apply Hs; lia.
    - unfold atx_cells0, kn_cells, tcells in *. cbn [map] in *.
      repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
      unfold ANEEDLOCKS, AX_FIN, AX_SLOT, AX_HEAD, AX_BUILTIN in *.
      repeat apply Forall_cons; try apply Forall_nil; (apply kword_cell; [cbn; lia | lia | cbn; lia | assumption]).
  Qed.

  Lemma regTf_denot : forall v regs, map (rdenot (MENV v regs)) regTf = regTf_w.
  Proof.
    intros v regs. unfold regTf, regTf_w, rdenot, estart. cbn [map fst snd a_base a_off edenot]. unfold AAEF.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. repeat f_equal; lia.
  Qed.
  Lemma regT0_denot : forall v regs, v_sp0 v = sp -> map (rdenot (MENV v regs)) regT0 = regT0_w sp.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs Ev. cbn in Ev. subst v0. unfold regT0, regT0_w, rdenot, estart. cbn [map fst snd a_base a_off]. evs.
    unfold AINIT, AX_SLOT, AX_F3, AX_A3. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. repeat f_equal; lia.
  Qed.

  Lemma regTf_flat : forall v regs, regions_flat (MENV v regs) regTf.
  Proof.
    intros v regs r Hr. unfold regTf in Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
    unfold flat, estart; cbn [fst snd a_base a_off edenot]. unfold AAEF. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
  Qed.
  Lemma regT0_flat : forall v regs, v_sp0 v = sp -> regions_flat (MENV v regs) regT0.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs Ev r Hr. cbn in Ev. subst v0. unfold regT0 in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    unfold flat, estart; cbn [fst snd a_base a_off]; evs; unfold AINIT, AX_SLOT, AX_F3, AX_A3; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
  Qed.

  Ltac mk_frameT v regs mem regs_ cov den flt EQM LF FR Ev :=
    pose proof (log_covered_frame (MENV v regs) mem regs_ _ cov (flt v regs Ev) LF) as FR;
    rewrite <- EQM, (den v regs Ev) in FR.

  Lemma stk_after : forall mem mem' rs, frame_mod mem mem' rs -> stk_ok RSEGS mem sp 128 -> stk_ok RSEGS mem' sp 128.
  Proof. intros mem mem' rs FM Hstk a m Ha Hm. eapply frame_mod_store_ok; [exact FM|]. apply Hstk; assumption. Qed.
  Lemma latch_after : forall mem mem' rs, frame_mod mem mem' rs -> latch_ok mem -> latch_ok mem'.
  Proof. intros mem mem' rs FM HL a m Ha Hm. eapply frame_mod_store_ok; [exact FM|]. apply HL; assumption. Qed.

  Definition tframe (mem : word -> option byte) (s0 s1 s2 s3 s4 s5 s6 s7 : word) : Prop :=
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ATR_MAINRET))
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = Some (word_to_le_bytes 8 s0)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8 = Some (word_to_le_bytes 8 s1)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8 = Some (word_to_le_bytes 8 s2)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 40)) 8 = Some (word_to_le_bytes 8 s3)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 48)) 8 = Some (word_to_le_bytes 8 s4)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 56)) 8 = Some (word_to_le_bytes 8 s5)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 64)) 8 = Some (word_to_le_bytes 8 s6)
    /\ rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 72)) 8 = Some (word_to_le_bytes 8 s7).

  Definition regs138 (regs : bvmap 5 word) (N PL cfg CP : word) : Prop :=
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 80) /\ getr regs 4 = Z_to_bv 64 0x6c5858 /\ getr regs 8 = N
    /\ getr regs 9 = PL /\ getr regs 18 = cfg /\ getr regs 19 = CP /\ getr regs 20 = Z_to_bv 64 AINIT.

  Definition loop_base (regs : bvmap 5 word) (N D OW : word) : Prop :=
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 80) /\ getr regs 4 = Z_to_bv 64 0x6c5858 /\ getr regs 8 = N
    /\ getr regs 9 = D /\ getr regs 18 = OW /\ getr regs 20 = Z_to_bv 64 AINIT
    /\ getr regs 22 = Z_to_bv 64 0 /\ getr regs 23 = Z_to_bv 64 MINUS2.

  Definition keep4 (regs regs' : bvmap 5 word) : Prop :=
    forall r : reg, In r [24; 25; 26; 27]%list -> getr regs' r = getr regs r.
  Ltac fin_keep4 HR' :=
    intros rr Hrr; cbn [In] in Hrr;
    destruct Hrr as [<-|[<-|[<-|[<-|[]]]]];
    [fin_reg HR' (24:reg) | fin_reg HR' (25:reg) | fin_reg HR' (26:reg) | fin_reg HR' (27:reg)].

  Lemma seg_T0 : forall s msF mo regs mem (CP cfg PL N : word) K,
    getr regs 1 = Z_to_bv 64 ATR_MAINRET -> getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 0x6c5858 ->
    getr regs 10 = CP -> getr regs 11 = cfg -> getr regs 12 = PL -> getr regs 13 = N ->
    rdn RSEGS mem (Z_to_bv 64 AINIT) 1 = Some [Z_to_bv 8 0] ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem -> atx_ok mem -> tcells mem atx_cells0 ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 ATR_POSTINIT) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        regs138 regs' N PL cfg CP ->
        keep4 regs regs' -> frame_mod mem mem' (regT0_w sp) -> stk_ok RSEGS mem' sp 128 ->
        tframe mem' (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) ->
        tcells mem' atx_cells1 ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_ENTRY) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem CP cfg PL N K R1 R2 R4 R10 R11 R12 R13 Hib Hstk Hro Hrel Hlatch Hatx HC0 HK HV HA.
    set (v := TV (Z_to_bv 64 0) cfg N (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) PL CP (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT00 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT0) by (apply knT0_ok; subst v; try assumption; reflexivity).
    assert (RD : sc_denot RSEGS mem (MENV v regs) (SCReadBase (SA (ELit 0) AINIT) 1 false (EVar 5))).
    { cbn [sc_denot]. unfold adenot, v_addi. cbn [a_base a_off edenot ev MENV mvals vals_ev nth app v_cap TV]. unfold AINIT in *.
      rewrite (u_small 0) by lia. cbn [Z.add]. exists [Z_to_bv 8 0]. split; [exact Hib|].
      rewrite bytes_le_to_Z_1. cbn [extz]. subst v. cbn [v_cap]. reflexivity. }
    run_segT STOPST scrT0b ATR_ENTRY srT00 knT0 46%nat rT0b cT0b (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HA |].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [| apply Forall_cons; [exact RD | apply Forall_nil]].
      subst v. cbn [sc_denot branch_taken edenot ev MENV mvals vals_ev nth app TV v_cap]. unfold bv_eqb. reflexivity. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT0b))) with ATR_POSTINIT. change (s_regs (fst (fst rT0b))) with srT0b in HR'.
    mk_frameT v regs mem regT0 covT0b regT0_denot regT0_flat EQM LF FR (@eq_refl word sp).
    apply (HK _ _ _ _ HV' HA' SB').
    + unfold regs138. subst v. repeat split;
        first [ fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg) ].
    + fin_keep4 HR'.
    + exact FR.
    + eapply stk_after; [exact FR | exact Hstk].
    + unfold tframe, ATR_MAINRET. subst v.
      repeat split;
        lazymatch goal with |- rdn _ _ (Z_to_bv 64 (bv_unsigned sp - ?k)) 8 = _ =>
          let off := eval vm_compute in (- k)%Z in
          krdv HK' 0%nat off 8%nat Hrd; [apply flat_intro; cbn [edenot ev MENV mvals vals_ev nth app TV v_sp0]; lia|];
          unfold adenot, v_addi in Hrd; cbn [a_base a_off edenot ev MENV mvals vals_ev nth app TV v_sp0] in Hrd;
          rewrite ?ev_junk in Hrd by lia;
          replace (bv_unsigned sp - k)%Z with (bv_unsigned sp + off)%Z by lia; exact Hrd
        end.
    + unfold atx_cells1, tcells, tcell, AX_SLOT, AX_F3, AX_A3, AINIT, ATEXIT_CALL_A, AEF_GUARD_A. subst v.
      repeat apply Forall_cons; try apply Forall_nil;
        lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) ?n = _ => krd HK' a n Hrd; exact Hrd end.
  Qed.

  Lemma vand3 : forall (c : byte), v_and (Z_to_bv 64 (bv_unsigned c)) (Z_to_bv 64 3) = Z_to_bv 64 (Z.land (bv_unsigned c) 3).
  Proof.
    intros c. pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn in Hc.
    unfold v_and. rewrite !u_small by lia. reflexivity.
  Qed.

  Definition calls_of (cfgz : Z) (c : byte) : Z := if (cfgz =? 0)%Z then 1 else (Z.land (bv_unsigned c) 3 + 1)%Z.

  Lemma seg_T1pos : forall s msF mo regs mem (Nz cfgz : Z) (PL CP : word) (c : byte) K,
    regs138 regs (Z_to_bv 64 Nz) PL (Z_to_bv 64 cfgz) CP -> (0 < Nz < 2 ^ 62)%Z -> (0 <= cfgz < 2 ^ 62)%Z ->
    (cfgz <> 0%Z -> rdn RSEGS mem CP 1 = Some [c]) -> (bv_unsigned CP + 1 < 2 ^ 64)%Z ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem ->
    (forall regs' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 ATR_JMALLOC) mem rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        regs138 regs' (Z_to_bv 64 Nz) PL (Z_to_bv 64 cfgz) CP -> getr regs' 21 = Z_to_bv 64 (calls_of cfgz c) ->
        keep4 regs regs' ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_POSTINIT) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem Nz cfgz PL CP c K (R2 & R4 & R8 & R9 & R18 & R19 & R20) HN Hcfg Hc HCP Hstk Hro Hrel Hlatch HK HV HA.
    pose proof (bv_unsigned_in_range 8 c) as Hc8. cbn in Hc8. pose proof (u64_range CP) as HCPr.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 cfgz) (Z_to_bv 64 Nz) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned c)) (Z_to_bv 64 0) PL CP (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT10 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    destruct (Z.eq_dec cfgz 0) as [C0|C0].
    - run_segT STOPST scrT1c ATR_POSTINIT srT10 knT 46%nat rT1c cT1c (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HA |].
      { sc_open; sc_eqb. }
      intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT1c))) with ATR_JMALLOC. change (s_regs (fst (fst rT1c))) with srT1c in HR'.
      cbn [mem_denot] in EQM. subst M'.
      apply (HK _ _ _ HV' HA' SB'); [| | fin_keep4 HR'].
      + unfold regs138. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg)].
      + unfold calls_of. rewrite (proj2 (Z.eqb_eq _ _) C0). fin_reg HR' (21:reg).
    - run_segT STOPST scrT1a ATR_POSTINIT srT10 knT 46%nat rT1a cT1a (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HA |].
      { sc_open.
        - sc_eqb.
        - unfold adenot, v_addi. cbn [a_base a_off]. evs. exists [c]. split; [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (Hc C0) | rewrite bytes_le_to_Z_1; reflexivity].
        - apply flat_intro; unfold elenZ; evs; unorm; rewrite ?u_small by lia; lia.
        - sc_eqb. }
      intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT1a))) with ATR_JMALLOC. change (s_regs (fst (fst rT1a))) with srT1a in HR'.
      cbn [mem_denot] in EQM. subst M'.
      apply (HK _ _ _ HV' HA' SB'); [| | fin_keep4 HR'].
      + unfold regs138. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg)].
      + unfold calls_of. rewrite (proj2 (Z.eqb_neq _ _) C0). unset_v. regv HR' (21:reg). cbn [edenot]. evs.
        rewrite alu_add, alu_and, vand3, vadd_ZZ. reflexivity.
  Qed.

  Lemma seg_T1zero : forall s msF mo regs mem (cfgz : Z) (PL CP : word) (c : byte) K,
    regs138 regs (Z_to_bv 64 0) PL (Z_to_bv 64 cfgz) CP -> (0 <= cfgz < 2 ^ 62)%Z ->
    (cfgz <> 0%Z -> rdn RSEGS mem CP 1 = Some [c]) -> (bv_unsigned CP + 1 < 2 ^ 64)%Z ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem ->
    (forall regs' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 ATR_CALLHEAD) mem rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        loop_base regs' (Z_to_bv 64 0) (Z_to_bv 64 AEMPTY) (Z_to_bv 64 0) -> getr regs' 21 = Z_to_bv 64 (calls_of cfgz c) ->
        keep4 regs regs' ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_POSTINIT) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem cfgz PL CP c K (R2 & R4 & R8 & R9 & R18 & R19 & R20) Hcfg Hc HCP Hstk Hro Hrel Hlatch HK HV HA.
    pose proof (bv_unsigned_in_range 8 c) as Hc8. cbn in Hc8. pose proof (u64_range CP) as HCPr.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 cfgz) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned c)) (Z_to_bv 64 0) PL CP (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT10 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    destruct (Z.eq_dec cfgz 0) as [C0|C0].
    - run_segT STOPST scrT1d ATR_POSTINIT srT10 knT 46%nat rT1d cT1d (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HA |].
      { sc_open; sc_eqb. }
      intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT1d))) with ATR_CALLHEAD. change (s_regs (fst (fst rT1d))) with srT1d in HR'.
      cbn [mem_denot] in EQM. subst M'.
      apply (HK _ _ _ HV' HA' SB'); [| | fin_keep4 HR'].
      + unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
      + unfold calls_of. rewrite (proj2 (Z.eqb_eq _ _) C0). fin_reg HR' (21:reg).
    - run_segT STOPST scrT1b ATR_POSTINIT srT10 knT 46%nat rT1b cT1b (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HA |].
      { sc_open.
        - sc_eqb.
        - unfold adenot, v_addi. cbn [a_base a_off]. evs. exists [c]. split; [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (Hc C0) | rewrite bytes_le_to_Z_1; reflexivity].
        - apply flat_intro; unfold elenZ; evs; unorm; rewrite ?u_small by lia; lia.
        - sc_eqb. }
      intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT1b))) with ATR_CALLHEAD. change (s_regs (fst (fst rT1b))) with srT1b in HR'.
      cbn [mem_denot] in EQM. subst M'.
      apply (HK _ _ _ HV' HA' SB'); [| | fin_keep4 HR'].
      + unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
      + unfold calls_of. rewrite (proj2 (Z.eqb_neq _ _) C0). unset_v. regv HR' (21:reg). cbn [edenot]. evs.
        rewrite alu_add, alu_and, vand3, vadd_ZZ. reflexivity.
  Qed.

  Lemma seg_T2 : forall s msF mo regs mem (N PL cfg CP r : word) K,
    regs138 regs N PL cfg CP -> getr regs 21 = r ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem ->
    (forall regs' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xba108) mem rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        regs138 regs' N PL cfg CP -> getr regs' 21 = r -> getr regs' 1 = Z_to_bv 64 ATR_RET_MALLOC -> getr regs' 10 = N ->
        keep4 regs regs' ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_JMALLOC) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem N PL cfg CP r K (R2 & R4 & R8 & R9 & R18 & R19 & R20) R21 Hstk Hro Hrel Hlatch HK HV HA.
    set (v := TV (Z_to_bv 64 0) cfg N (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) r PL CP (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT20 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST noscr ATR_JMALLOC srT20 knT 46%nat rT2 cT2 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact HV | exact HA |].
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT2))) with 0xba108%Z. change (s_regs (fst (fst rT2))) with srT2 in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply (HK _ _ _ HV' HA' SB'); [| fin_reg HR' (21:reg) | fin_reg HR' (1:reg) | fin_reg HR' (10:reg) | fin_keep4 HR'].
    unfold regs138. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg)].
  Qed.

  Lemma seg_T3 : forall s msF mo regs mem (N PL cfg CP r D : word) K,
    regs138 regs N PL cfg CP -> getr regs 21 = r -> getr regs 10 = D -> (bv_unsigned D <> 0)%Z ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem ->
    (forall regs' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xb8580) mem rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        regs138 regs' N PL D CP -> getr regs' 21 = r -> getr regs' 1 = Z_to_bv 64 ATR_RET_MEMCPY ->
        getr regs' 10 = D -> getr regs' 11 = PL -> getr regs' 12 = N ->
        keep4 regs regs' ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_RET_MALLOC) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem N PL cfg CP r D K (R2 & R4 & R8 & R9 & R18 & R19 & R20) R21 R10 HD Hstk Hro Hrel Hlatch HK HV HA.
    set (v := TV (Z_to_bv 64 0) cfg N D (Z_to_bv 64 0) (Z_to_bv 64 0) r PL CP (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT30 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST scrT3 ATR_RET_MALLOC srT30 knT 46%nat rT3 cT3 (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HA |].
    { sc_open. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. exact HD. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT3))) with 0xb8580%Z. change (s_regs (fst (fst rT3))) with srT3 in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply (HK _ _ _ HV' HA' SB'); [| fin_reg HR' (21:reg) | fin_reg HR' (1:reg) | fin_reg HR' (10:reg) | fin_reg HR' (11:reg) | fin_reg HR' (12:reg) | fin_keep4 HR'].
    unfold regs138. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg)].
  Qed.

  Lemma seg_T4 : forall s msF mo regs mem (N PL cfg CP r D : word) K,
    regs138 regs N PL D CP -> getr regs 21 = r ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem ->
    (forall regs' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 ATR_CALLHEAD) mem rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        loop_base regs' N D D -> getr regs' 21 = r ->
        keep4 regs regs' ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_RET_MEMCPY) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem N PL cfg CP r D K (R2 & R4 & R8 & R9 & R18 & R19 & R20) R21 Hstk Hro Hrel Hlatch HK HV HA.
    set (v := TV (Z_to_bv 64 0) cfg N D (Z_to_bv 64 0) (Z_to_bv 64 0) r PL CP (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT40 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST noscr ATR_RET_MEMCPY srT40 knT 46%nat rT4 cT4 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact HV | exact HA |].
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT4))) with ATR_CALLHEAD. change (s_regs (fst (fst rT4))) with srT4 in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply (HK _ _ _ HV' HA' SB'); [| fin_reg HR' (21:reg) | fin_keep4 HR'].
    unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
  Qed.

  Ltac krd_cell HK' := unfold tcell, AAEF; lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) ?n = _ => let Hrd := fresh "Hrd" in krd HK' a n Hrd; exact Hrd end.

  Lemma seg_T5 : forall s msF mo regs mem (N D OW S3 r : word) K,
    loop_base regs N D OW -> getr regs 19 = S3 -> getr regs 21 = r ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xe8894) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        loop_base regs' N D OW -> getr regs' 19 = S3 -> getr regs' 21 = r -> getr regs' 1 = Z_to_bv 64 ATR_RET_LLVM ->
        getr regs' 10 = D -> getr regs' 11 = N ->
        keep4 regs regs' -> frame_mod mem mem' regTf_w -> stk_ok RSEGS mem' sp 128 -> latch_ok mem' ->
        tcell mem' (AAEF, 1%nat, 1%Z) ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_CALLHEAD) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem N D OW S3 r K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) R19 R21 Hstk Hro Hrel Hlatch HK HV HA.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 0) N D (Z_to_bv 64 0) (Z_to_bv 64 0) r (Z_to_bv 64 0) (Z_to_bv 64 0) OW S3).
    assert (HR : regs_ok (MENV v regs) srT50 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST noscr ATR_CALLHEAD srT50 knT 46%nat rT5 cT5 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact HV | exact HA |].
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT5))) with 0xe8894%Z. change (s_regs (fst (fst rT5))) with srT5 in HR'.
    pose proof (log_covered_frame (MENV v regs) mem regTf _ covT5 (regTf_flat v regs) LF) as FR. rewrite <- EQM, (regTf_denot v regs) in FR.
    apply (HK _ _ _ _ HV' HA' SB'); [| fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (1:reg) | fin_reg HR' (10:reg) | fin_reg HR' (11:reg) | fin_keep4 HR'
                                   | exact FR | eapply stk_after; [exact FR | exact Hstk] | eapply latch_after; [exact FR | exact Hlatch] | krd_cell HK'].
    unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
  Qed.

  Lemma seg_T6 : forall s msF mo regs mem (N D OW r : word) K,
    loop_base regs N D OW -> getr regs 21 = r -> getr regs 10 = Z_to_bv 64 0 ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem ->
    (forall regs' mem' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xe884c) mem' rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        loop_base regs' N D OW -> getr regs' 19 = Z_to_bv 64 0 -> getr regs' 21 = r -> getr regs' 1 = Z_to_bv 64 ATR_RET_EMIT ->
        getr regs' 11 = Z_to_bv 64 0 ->
        keep4 regs regs' -> frame_mod mem mem' regTf_w -> stk_ok RSEGS mem' sp 128 -> latch_ok mem' ->
        tcell mem' (AAEF, 1%nat, 0%Z) ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_RET_LLVM) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem N D OW r K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) R21 R10 Hstk Hro Hrel Hlatch HK HV HA.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 0) N D (Z_to_bv 64 0) (Z_to_bv 64 0) r (Z_to_bv 64 0) (Z_to_bv 64 0) OW (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT60 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    run_segT STOPST noscr ATR_RET_LLVM srT60 knT 46%nat rT6 cT6 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact HV | exact HA |].
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT6))) with 0xe884c%Z. change (s_regs (fst (fst rT6))) with srT6 in HR'.
    pose proof (log_covered_frame (MENV v regs) mem regTf _ covT6 (regTf_flat v regs) LF) as FR. rewrite <- EQM, (regTf_denot v regs) in FR.
    apply (HK _ _ _ _ HV' HA' SB'); [| fin_reg HR' (19:reg) | fin_reg HR' (21:reg) | fin_reg HR' (1:reg) | fin_reg HR' (11:reg) | fin_keep4 HR'
                                   | exact FR | eapply stk_after; [exact FR | exact Hstk] | eapply latch_after; [exact FR | exact Hlatch] | krd_cell HK'].
    unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
  Qed.

  Lemma decw_val : forall (E : env) (rz : Z), (1 <= rz <= 4)%Z -> ev E 7 = Z_to_bv 64 rz ->
    edenot E (EAluw ALU_ADD (EVar 7) (ELit (-1))) = Z_to_bv 64 (rz - 1).
  Proof.
    intros E rz Hr H7. cbn [edenot]. rewrite H7.
    assert (C : (rz = 1 \/ rz = 2 \/ rz = 3 \/ rz = 4)%Z) by lia.
    destruct C as [-> | [-> | [-> | ->]]]; apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma seg_T7more : forall s msF mo regs mem (N D OW : word) (rz : Z) K,
    loop_base regs N D OW -> getr regs 19 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 rz -> (2 <= rz <= 4)%Z ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem ->
    (forall regs' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 ATR_CALLHEAD) mem rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        loop_base regs' N D OW -> getr regs' 21 = Z_to_bv 64 (rz - 1) ->
        keep4 regs regs' ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_RET_EMIT) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem N D OW rz K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) R19 R21 Hr Hstk Hro Hrel Hlatch HK HV HA.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 0) N D (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 rz) (Z_to_bv 64 0) (Z_to_bv 64 0) OW (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT70 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    assert (DW : edenot (MENV v regs) (EAluw ALU_ADD (EVar 7) (ELit (-1))) = Z_to_bv 64 (rz - 1)) by (apply decw_val; [lia | reflexivity]).
    run_segT STOPST scrT7a ATR_RET_EMIT srT70 knT 46%nat rT7a cT7a (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HA |].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [|apply Forall_nil]. cbn [sc_denot branch_taken]. rewrite DW, ed_lit. unfold bv_eqb.
      rewrite !u_small by lia. rewrite Bool.negb_true_iff. apply Z.eqb_neq. lia. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT7a))) with ATR_CALLHEAD. change (s_regs (fst (fst rT7a))) with srT7a in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply (HK _ _ _ HV' HA' SB'); [| regv HR' (21:reg); exact DW | fin_keep4 HR'].
    unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
  Qed.

  Lemma seg_T7free : forall s msF mo regs mem (N D OW : word) K,
    loop_base regs N D OW -> getr regs 19 = Z_to_bv 64 0 -> getr regs 21 = Z_to_bv 64 1 ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem ->
    (forall regs' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 0xba104) mem rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        loop_base regs' N D OW -> getr regs' 1 = Z_to_bv 64 ATR_RET_FREE -> getr regs' 10 = OW ->
        keep4 regs regs' ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_RET_EMIT) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem N D OW K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) R19 R21 Hstk Hro Hrel Hlatch HK HV HA.
    set (v := TV (Z_to_bv 64 0) (Z_to_bv 64 0) N D (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) OW (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT70 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT) by (apply knT_ok; subst v; try assumption; reflexivity).
    assert (DW : edenot (MENV v regs) (EAluw ALU_ADD (EVar 7) (ELit (-1))) = Z_to_bv 64 (1 - 1)) by (apply decw_val; [lia | reflexivity]).
    run_segT STOPST scrT7b ATR_RET_EMIT srT70 knT 46%nat rT7b cT7b (MENV v regs) mem regs; [exact HR | exact HKn | | exact HV | exact HA |].
    { lazymatch goal with |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l' end.
      apply Forall_cons; [|apply Forall_nil]. cbn [sc_denot branch_taken]. rewrite DW, ed_lit. reflexivity. }
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT7b))) with 0xba104%Z. change (s_regs (fst (fst rT7b))) with srT7b in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply (HK _ _ _ HV' HA' SB'); [| fin_reg HR' (1:reg) | fin_reg HR' (10:reg) | fin_keep4 HR'].
    unfold loop_base. repeat split; [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg) | fin_reg HR' (18:reg) | fin_reg HR' (20:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg)].
  Qed.

  Lemma knT8_ok : forall v regs mem (s0 s1 s2 s3 s4 s5 s6 s7 : word),
    v_sp0 v = sp -> v_tid v = s0 -> v_pp v = s1 -> v_A v = s2 -> v_len v = s3 -> v_cap v = s4 -> v_A2 v = s5 -> v_b8 v = s6 -> v_b9 v = s7 ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem -> tframe mem s0 s1 s2 s3 s4 s5 s6 s7 ->
    know_ok RSEGS (MENV v regs) mem knT8.
  Proof.
    intros [v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13] regs mem s0 s1 s2 s3 s4 s5 s6 s7 E0 E1 E2 E3 E4 E5 E6 E8 E9 Hstk Hro Hrel Hlatch
           (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    cbn in E0, E1, E2, E3, E4, E5, E6, E8, E9. subst.
    unfold knT8. unfold know_ok. apply Forall_app. split; [| apply (knT_ok (MV sp s0 s1 s2 s3 s4 s5 v7 s6 s7 v10 v11 v12 v13) regs mem eq_refl Hstk Hro Hrel Hlatch)].
    repeat (apply Forall_cons); [ .. | apply Forall_nil].
    all: lazymatch goal with |- kentry_ok _ _ _ (KWord (SA (EVar 0) ?k) 8 ?e) =>
           eapply (kword_intro RSEGS _ mem (EVar 0) sp k 8 e); [reflexivity | evs; reflexivity | lia | lia | lia | lia |];
           replace (bv_unsigned sp + k)%Z with (bv_unsigned sp - (- k))%Z by lia; cbn [Z.opp Pos.succ]; assumption
         end.
  Qed.

  Lemma seg_T8 : forall s msF mo regs mem (N D OW s0 s1 s2 s3 s4 s5 s6 s7 : word) K,
    loop_base regs N D OW ->
    stk_ok RSEGS mem sp 128 -> aro_none mem -> arelro_none mem -> latch_ok mem -> tframe mem s0 s1 s2 s3 s4 s5 s6 s7 ->
    (forall regs' msF' mo',
        as_VIS H s msF' = mkst regs' (Z_to_bv 64 ATR_MAINRET) mem rom -> as_AKREL H s (mkCfg msF' mo') -> same_but_materialized mo mo' ->
        getr regs' 2 = sp -> getr regs' 4 = Z_to_bv 64 0x6c5858 -> getr regs' 10 = Z_to_bv 64 0 ->
        getr regs' 8 = s0 -> getr regs' 9 = s1 -> getr regs' 18 = s2 -> getr regs' 19 = s3 -> getr regs' 20 = s4 -> getr regs' 21 = s5 ->
        getr regs' 22 = s6 -> getr regs' 23 = s7 ->
        (forall r : reg, In r [3; 24; 25; 26; 27]%list -> getr regs' r = getr regs r) ->
        keep4 regs regs' ->
        realizes asegs (mkCfg msF' mo') K) ->
    as_VIS H s msF = mkst regs (Z_to_bv 64 ATR_RET_FREE) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem N D OW s0 s1 s2 s3 s4 s5 s6 s7 K (R2 & R4 & R8 & R9 & R18 & R20 & R22 & R23) Hstk Hro Hrel Hlatch TF HK HV HA.
    set (v := MV sp s0 s1 s2 s3 s4 s5 (Z_to_bv 64 0) s6 s7 OW (getr regs 19) (Z_to_bv 64 0) (Z_to_bv 64 0)).
    assert (HR : regs_ok (MENV v regs) srT80 regs) by (subst v; prove_regs_ok).
    assert (HKn : know_ok RSEGS (MENV v regs) mem knT8) by (eapply knT8_ok; subst v; try eassumption; reflexivity).
    run_segT STOPST noscr ATR_RET_FREE srT80 knT8 46%nat rT8 cT8 (MENV v regs) mem regs; [exact HR | exact HKn | scs_nil | exact HV | exact HA |].
    intros R' M' msF' mo' HR' HK' EQM LF HV' HA' SB'. change (s_pc (fst (fst rT8))) with ATR_MAINRET. change (s_regs (fst (fst rT8))) with srT8 in HR'.
    cbn [mem_denot] in EQM. subst M'.
    apply (HK _ _ _ HV' HA' SB'); [fin_reg HR' (2:reg) | fin_reg HR' (4:reg) | fin_reg HR' (10:reg) | fin_reg HR' (8:reg) | fin_reg HR' (9:reg)
              | fin_reg HR' (18:reg) | fin_reg HR' (19:reg) | fin_reg HR' (20:reg) | fin_reg HR' (21:reg) | fin_reg HR' (22:reg) | fin_reg HR' (23:reg) | | fin_keep4 HR'].
    intros r Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
      [fin_reg HR' (3:reg) | fin_reg HR' (24:reg) | fin_reg HR' (25:reg) | fin_reg HR' (26:reg) | fin_reg HR' (27:reg)].
  Qed.
End BlocksT.
