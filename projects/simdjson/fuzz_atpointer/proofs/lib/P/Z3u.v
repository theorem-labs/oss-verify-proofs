(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z9l Z9m Zb0 Z9n Z9o Z44.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma out_recast {CE__ : Ceiling} : forall m A (w0 w1 e : word) (od : list byte),
  rw_cells psegs m A [C8 w0; C8 w1; C4 e; CB 4 od] -> rw_cells psegs m A [CB 8 (le8 w0); CB 8 (le8 w1); CB 4 (le4 e); CB 4 od].
Proof.
  intros m A w0 w1 e od H. eapply rw_cells_recast; [exact H| | reflexivity| reflexivity].
  destruct H as [[W _] _]. cbn [cells_wf cell_wf] in W |- *. rewrite length_le8, length_le8, length_le4. tauto.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Arr.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_stmt E d.

  Lemma arr_digit_loop : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (rest : list Z) (Pr L tz spv : Z)
      (x1 x3 x8 x11 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 wt1 : word),
    bytes_at psegs m Pr (map (Z_to_bv 8) rest) -> Forall (fun c => 0 <= c < 256) rest -> L = zlength rest ->
    0 < Pr -> Pr + L < 2^63 -> tz = - L -> mem_inv psegs m ->
    (forall (code : Z) (xs1 xa3 xa5 xa6 xt5 xt6 : word), 0 <= code < 64 ->
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 tz) wt1 (Z_to_bv 64 9) x8 xs1
                          (Z_to_bv 64 L) x11 (Z_to_bv 64 Pr) xa3 (Z_to_bv 64 code) xa5 xa6 (Z_to_bv 64 47)
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 10) (Z_to_bv 64 48) xt5 xt6)
                     F (Z_to_bv 64 0x2882c) fc None m (seg_rom psegs))) ->
    (forall (tok c3 : Z) (xs1 xa5 xa6 xt5 xt6 : word),
       0 <= tok <= L -> (forall j, (j < Z.to_nat tok)%nat -> nth j rest 0 <> 47) ->
       ((c3 = 47 /\ tok < L /\ nth (Z.to_nat tok) rest 0 = 47) \/ (c3 <> 47 /\ tok = L)) -> 0 <= c3 < 256 ->
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 tz) wt1 (Z_to_bv 64 9) x8 xs1
                          (Z_to_bv 64 L) x11 (Z_to_bv 64 Pr) (Z_to_bv 64 c3) (Z_to_bv 64 tok) xa5 xa6 (Z_to_bv 64 47)
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 10) (Z_to_bv 64 48) xt5 xt6)
                     F (Z_to_bv 64 0x287d4) fc None m (seg_rom psegs))) ->
    forall (n : nat) (cnt : Z) (xs1 xa3 xa5 xt6 : word),
      0 <= cnt < L -> L - cnt <= Z.of_nat n -> (forall j, (j < Z.to_nat cnt)%nat -> nth j rest 0 <> 47) ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 tz) wt1 (Z_to_bv 64 9) x8 xs1
                         (Z_to_bv 64 L) x11 (Z_to_bv 64 Pr) xa3 (Z_to_bv 64 22) xa5 (Z_to_bv 64 (- cnt)) (Z_to_bv 64 47)
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 10) (Z_to_bv 64 48) (Z_to_bv 64 (Pr + cnt)) xt6)
                    F (Z_to_bv 64 0x28760) fc None m (seg_rom psegs)).
  Proof.
    intros K m F fc rest Pr L tz spv x1 x3 x8 x11 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 wt1 RB RF EL P0 PL TZ MI XERR XTOK.
    induction n as [|n IH]; intros cnt xs1 xa3 xa5 xt6 CR FUEL NOSL; [lia|].
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    set (c := nth (Z.to_nat cnt) rest 0).
    assert (CB : 0 <= c < 256) by (subst c; apply Forall_nth_Z; [exact RF| unfold zlength in *; lia]).
    pose proof (zbytes_read1 m Pr rest cnt RB ltac:(lia)) as RD. fold c in RD.

    astep. step. if_cases KS; zify_cond KS.
    {
      step. if_cases KZ.
      - eapply evt_eq; [| eapply (XERR 22)]; [atp_st_eq| lia].
      - astep. eapply evt_eq; [| eapply (XTOK cnt 47)]; [atp_st_eq| lia| exact NOSL| left; subst c; split; [reflexivity| split; [lia| exact KS]]| lia]. }

    astep. astep. step. if_cases KD.
    {   astep. step. eapply evt_eq; [| eapply (XERR 17)]; [atp_st_eq| lia]. }

    assert (AT684 : forall xs1' xt6' : word,
      evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 tz) wt1 (Z_to_bv 64 9) x8 xs1'
                         (Z_to_bv 64 L) x11 (Z_to_bv 64 Pr) (Z_to_bv 64 c) (Z_to_bv 64 22) xa5 (Z_to_bv 64 (- cnt)) (Z_to_bv 64 47)
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 10) (Z_to_bv 64 48) (Z_to_bv 64 (Pr + cnt))
                         xt6')
                    F (Z_to_bv 64 0x28780) fc None m (seg_rom psegs))).
    { intros xs1' xt6'.

      astep. astep. astep. step. if_cases KO.
      {   astep. eapply evt_eq; [| eapply (XERR 19)]; [atp_st_eq| lia]. }

      assert (NOSL1 : forall j, (j < Z.to_nat (cnt + 1))%nat -> nth j rest 0 <> 47).
      { intros j Hj. destruct (Nat.eq_dec j (Z.to_nat cnt)) as [->|NE]; [exact KS|]. apply NOSL. lia. }
      astep. astep. astep. astep. step. if_cases KL; zify_cond KL; rewrite ?land64_mod in KL.
      -
        assert (NE : cnt + 1 <> L) by (intros EQ; apply KL; rewrite TZ, <- EQ; f_equal; lia).
        eapply evt_eq; [| eapply (IH (cnt + 1))]; [atp_st_eq| lia| lia| exact NOSL1].
      -
        assert (EQ : cnt + 1 = L) by (rewrite TZ in KL; lia).
        astep. step. eapply evt_eq; [| eapply (XTOK L c)]; [atp_st_eq| lia| rewrite <- EQ; exact NOSL1| right; split; [exact KS| reflexivity]| lia]. }

    pose proof (zbytes_read1 m Pr rest 0 RB ltac:(lia)) as RDZ. rewrite Z.add_0_r in RDZ.
    assert (C0B : 0 <= nth (Z.to_nat 0) rest 0 < 256) by (apply Forall_nth_Z; [exact RF| unfold zlength in *; lia]).
    step. if_cases KZ2.
    { eapply evt_eq; [| eapply AT684]; [atp_st_eq]. }
    astep. step. if_cases KZ3.
    all: first [eapply evt_eq; [| eapply AT684]; [atp_st_eq] | eapply evt_eq; [| eapply (XERR 22)]; [atp_st_eq| lia]].
  Qed.

  Lemma arr_iter_loop : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (e cc spv : Z)
      (x1 x3 x8 xa0 xa2 xa3 xa4 xa6 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word),
    bytes_at psegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) -> e + 1 <= Z.of_nat (length (ae_tws E)) - 1 -> mem_inv psegs m ->
    (forall (it j' : Z) (xs1 xa5 xt5 xt6 : word),
       elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d it j' -> 0 <= it -> j' <= e ->
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 e) (Z_to_bv 64 32) (Z_to_bv 64 4294967295) x8 xs1
                          xa0 (Z_to_bv 64 it) xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (ae_TAPE E))
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) xt5 xt6)
                     F (Z_to_bv 64 0x2890c) fc None m (seg_rom psegs))) ->
    (forall (xs1 xa1 xa5 xt5 xt6 : word),
       evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 e) (Z_to_bv 64 32) (Z_to_bv 64 4294967295) x8 xs1
                          xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (ae_TAPE E))
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) xt5 xt6)
                     F (Z_to_bv 64 0x28868) fc None m (seg_rom psegs))) ->
    forall (n : nat) (it c' : Z) (xs1 xa5 xt5 xt6 : word),
      tiles (elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d) it e c' -> it <> e -> 0 <= it -> e - it <= Z.of_nat n ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 e) (Z_to_bv 64 32) (Z_to_bv 64 4294967295) x8 xs1
                         xa0 (Z_to_bv 64 it) xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (ae_TAPE E))
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) xt5 xt6)
                    F (Z_to_bv 64 0x288b0) fc None m (seg_rom psegs)).
  Proof.
    intros K m F fc e cc spv x1 x3 x8 xa0 xa2 xa3 xa4 xa6 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 TAPEB EN MI XFOUND XNF.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ _ _].
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : Z.of_nat (length (ae_sbs E)) < 2^56) by (destruct WF as (_ & ? & _); lia).
    induction n as [|n IH]; intros it c' xs1 xa5 xt5 xt6 TI NE I0 FUEL.
    { pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TI). lia. }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (array_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE I0 ltac:(lia)) as (j' & EL & IJ & AFT & TI').

    astep. step. if_cases KF.
    { eapply evt_eq; [| eapply (XFOUND it j')]; [atp_st_eq| exact EL| exact I0| lia]. }
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDT.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (Tf (ae_tws E) it) < 256) by (unfold ttype; lia).

    astep. astep. step. astep.

    assert (NEXT : forall (pc : Z) (xs1' xt6' : word), (pc = 0x288e0 \/ pc = 0x288f8 \/ pc = 0x28904) ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 e) (Z_to_bv 64 32) (Z_to_bv 64 4294967295) x8 xs1'
                         xa0 (Z_to_bv 64 j') xa2 xa3 xa4 (Z_to_bv 64 (bv_unsigned xa5 + -1)) xa6 (Z_to_bv 64 (ae_TAPE E))
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297)
                         (Z_to_bv 64 (Tf (ae_tws E) it)) xt6')
                    F (Z_to_bv 64 pc) fc None m (seg_rom psegs))).
    { intros pc xs1' xt6' [-> |[-> | ->]]; (step; if_cases KL; zify_cond KL;
        [ eapply (IH j' (c' - 1)); [exact TI'| exact KL| lia| lia]
        | step; apply XNF ]). }

    destruct (elem_view_of (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any (fun c cv H => H) HSN d it j' EL I0 ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    -
      unfold t_true, t_false, t_null in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (astep; step; if_false; astep; astep; step; if_true; astep; astep; step; if_true; astep;
         eapply evt_eq; [| eapply (NEXT 0x28904)]; [atp_st_eq| do 2 right; reflexivity]).
    -
      unfold t_i64, t_u64, t_dbl in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (astep; step; if_false; astep; astep; step; if_false; astep;
         eapply evt_eq; [| eapply (NEXT 0x288e0)]; [atp_st_eq| left; reflexivity]).
    -
      unfold t_str in TY. rewrite TY.
      astep. step. if_true. astep.
      eapply evt_eq; [| eapply (NEXT 0x28904)]; [atp_st_eq| do 2 right; reflexivity].
    -
      unfold t_arr in TY. rewrite TY.
      astep. step. if_false. astep. astep. step. if_true. astep. astep. step. if_false. astep.
      rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0x288f8)]; [atp_st_eq| right; left; reflexivity].
    -
      unfold t_obj in TY. rewrite TY.
      astep. step. if_false. astep. astep. step. if_true. astep. astep. step. if_false. astep.
      rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0x288f8)]; [atp_st_eq| right; left; reflexivity].
  Qed.

End Arr.
End WithCeiling0.
