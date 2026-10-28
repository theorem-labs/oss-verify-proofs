(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_kitu.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma le8_nth7 : forall v, (0 <= v < 2^64)%Z -> nth 7 (le8 (Z_to_bv 64 v)) (Z_to_bv 8 0) = Z_to_bv 8 (ttype v).
Proof.
  intros v Hv. unfold le8, word_to_le_bytes. rewrite a_u64_small by lia.
  cbn [Z_to_le_bytes nth]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite a_shr56. reflexivity.
Qed.

Lemma u64s_read7 : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 1 (skipn (8 * i + 7) (u64s ws)) = [nth 7 (le8 (nth i ws (Z_to_bv 64 0))) (Z_to_bv 8 0)].
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - cbn [Nat.mul Nat.add u64s nth]. rewrite skipn_app, length_le8. replace (7 - 8)%nat with 0%nat by lia. cbn [skipn].
    pose proof (length_le8 w) as L. remember (le8 w) as l eqn:El. clear El.
    destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 r]]]]]]]]]; cbn [length] in L; try lia. reflexivity.
  - replace (8 * S i + 7)%nat with (8 + (8 * i + 7))%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + (8 * i + 7) - 8)%nat with (8 * i + 7)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma tape_read_type : forall m TAPE (tws : list Z) (i : Z),
  bytes_at usegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes usegs m (wa (TAPE + 8 * i + 7)) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HT.
  replace (TAPE + 8 * i + 7) with (TAPE + (8 * i + 7)) by lia.
  rewrite (bytes_at_read usegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal. replace (Z.to_nat (8 * i + 7)) with (8 * Z.to_nat i + 7)%nat by lia.
  rewrite u64s_read7 by (rewrite length_map; lia).
  rewrite <- le8_nth7 by exact HT. do 3 f_equal.
  unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
Qed.

Lemma substr_cps : forall Q (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SV A n pos RA : Z),
  rw_cells usegs m SV [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 n)] -> 0 <= pos <= n -> 0 < A -> A + n < 2^63 -> n - pos < bv_unsigned a2 ->
  0 <= SV -> SV + 16 < 2^64 -> ra = Z_to_bv 64 RA -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
  (forall (xa3 xa4 xa5 : word),
     evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (A + pos)) (Z_to_bv 64 (n - pos)) a2 xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 RA) fc None m (seg_rom usegs))) ->
  evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 SV) (Z_to_bv 64 pos) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x3e478) fc None m (seg_rom usegs)).
Proof.
  intros until RA. intros SVC POS A0 AN NA2 SV0 SV64 -> RA0 RA2 HK.
  pose proof (bv_unsigned_in_range 64 a2) as A2R. unfold bv_modulus in A2R. cbn in A2R.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. step. if_lia. step. astep. step. if_lia.

  astep. astep.
  replace (0 <? A) with true by (symmetry; apply Z.ltb_lt; lia).
  first [ replace (pos + A <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
        | replace (A + pos <? 1) with false by (symmetry; apply Z.ltb_ge; lia) ].
  cbn [Z.b2z Z.lxor Pos.lxor]. astep. step. if_false.

  astep. step. if_lia. step.
  replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
  eapply evt_eq; [| eapply HK]. atp_st_eq.
Qed.

Section ArrL.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.

  Lemma arr_digit_loop : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (rest : list Z) (Pr L tz spv : Z)
      (x1 x3 x8 x9 x19 x20 x21 x22 x23 x24 x25 x26 x27 wdiv : word),
    bytes_at usegs m Pr (map (Z_to_bv 8) rest) -> Forall (fun c => 0 <= c < 256) rest -> L = zlength rest ->
    0 < Pr -> Pr + L < 2^63 -> tz = - L -> mem_inv usegs m ->
    (forall (code : Z) (xa2 xa3 xt3 xt4 xt5 xt6 xs2 : word), 0 < code < 64 ->
       evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 48) x8 x9
                          (Z_to_bv 64 Pr) (Z_to_bv 64 code) xa2 xa3 (Z_to_bv 64 tz) (Z_to_bv 64 1) (Z_to_bv 64 47) wdiv
                          xs2 x19 x20 x21 x22 x23 x24 x25 x26 x27 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x3f5c4) fc None m (seg_rom usegs))) ->
    (forall (tok : Z) (xa2 xa3 xt3 xt4 xt5 xt6 : word),
       0 <= tok <= L -> (forall j, (j < Z.to_nat tok)%nat -> nth j rest 0 <> 47) ->
       ((tok < L /\ nth (Z.to_nat tok) rest 0 = 47) \/ tok = L) ->
       evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 48) x8 x9
                          (Z_to_bv 64 Pr) (Z_to_bv 64 22) xa2 xa3 (Z_to_bv 64 tz) (Z_to_bv 64 1) (Z_to_bv 64 47) wdiv
                          (Z_to_bv 64 tok) x19 x20 x21 x22 x23 x24 x25 x26 x27 xt3 xt4 xt5 xt6)
                     F (Z_to_bv 64 0x3f52c) fc None m (seg_rom usegs))) ->
    forall (n : nat) (cnt : Z) (xa2 xt5 xt6 : word),
      0 <= cnt < L -> L - cnt <= Z.of_nat n -> (forall j, (j < Z.to_nat cnt)%nat -> nth j rest 0 <> 47) ->
      evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 48) x8 x9
                         (Z_to_bv 64 Pr) (Z_to_bv 64 22) xa2 (Z_to_bv 64 (- cnt)) (Z_to_bv 64 tz) (Z_to_bv 64 1) (Z_to_bv 64 47) wdiv
                         (Z_to_bv 64 L) x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (Pr + cnt)) (Z_to_bv 64 (Pr + cnt)) xt5 xt6)
                    F (Z_to_bv 64 0x3f4c0) fc None m (seg_rom usegs)).
  Proof.
    intros K m F fc rest Pr L tz spv x1 x3 x8 x9 x19 x20 x21 x22 x23 x24 x25 x26 x27 wdiv RB RF EL P0 PL TZ MI XERR XTOK.
    induction n as [|n IH]; intros cnt xa2 xt5 xt6 CR FUEL NOSL; [lia|].
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    set (c := nth (Z.to_nat cnt) rest 0).
    assert (CB : 0 <= c < 256) by (subst c; apply Forall_nth_Z; [exact RF| unfold zlength in *; lia]).
    pose proof (zbytes_read1 m Pr rest cnt RB ltac:(lia)) as RD. fold c in RD.

    step. if_lia. astep.
    replace (Pr + cnt <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. astep. cbn [Z.lxor Pos.lxor]. step. if_false.
    step. if_lia.

    astep. step. if_cases KS; zify_cond KS.
    {
      step. if_cases KZ.
      - eapply evt_eq; [| eapply (XERR 22)]; [atp_st_eq| lia].
      - astep. eapply evt_eq; [| eapply (XTOK cnt)]; [atp_st_eq| lia| exact NOSL| left; subst c; split; [lia| exact KS]]. }

    step. if_lia. astep. astep. step. if_cases KD.
    {   astep. step. eapply evt_eq; [| eapply (XERR 17)]; [atp_st_eq| lia]. }

    assert (AT60 : forall xt5' xt6' : word,
      evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 48) x8 x9
                         (Z_to_bv 64 Pr) (Z_to_bv 64 22) xa2 (Z_to_bv 64 (- cnt)) (Z_to_bv 64 tz) (Z_to_bv 64 1) (Z_to_bv 64 47) wdiv
                         (Z_to_bv 64 L) x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (Pr + cnt)) (Z_to_bv 64 (Pr + cnt))
                         xt5' xt6')
                    F (Z_to_bv 64 0x3f4f8) fc None m (seg_rom usegs))).
    { intros xt5' xt6'.

      astep. astep. astep. step. if_cases KO.
      {   astep. eapply evt_eq; [| eapply (XERR 19)]; [atp_st_eq| lia]. }

      assert (NOSL1 : forall j, (j < Z.to_nat (cnt + 1))%nat -> nth j rest 0 <> 47).
      { intros j Hj. destruct (Nat.eq_dec j (Z.to_nat cnt)) as [->|NE]; [exact KS|]. apply NOSL. lia. }
      astep. astep. astep. astep. astep. step. if_cases KL; zify_cond KL; rewrite ?land64_mod in KL.
      -
        assert (NE : cnt + 1 <> L) by (intros EQ; apply KL; rewrite TZ, <- EQ; f_equal; lia).
        eapply evt_eq; [| eapply (IH (cnt + 1))]; [atp_st_eq| lia| lia| exact NOSL1].
      -
        assert (EQ : cnt + 1 = L) by (rewrite TZ in KL; lia).
        step. eapply evt_eq; [| eapply (XTOK L)]; [atp_st_eq| lia| rewrite <- EQ; exact NOSL1| right; reflexivity]. }

    pose proof (zbytes_read1 m Pr rest 0 RB ltac:(lia)) as RDZ. rewrite Z.add_0_r in RDZ.
    assert (C0B : 0 <= nth (Z.to_nat 0) rest 0 < 256) by (apply Forall_nth_Z; [exact RF| unfold zlength in *; lia]).
    step. if_cases KZ2.
    { eapply evt_eq; [| eapply AT60]; [atp_st_eq]. }
    astep. step. if_cases KZ3.
    all: first [eapply evt_eq; [| eapply AT60]; [atp_st_eq] | eapply evt_eq; [| eapply (XERR 22)]; [atp_st_eq| lia]].
  Qed.
End ArrL.

Lemma firstn4_le8 : forall v : word, firstn 4 (le8 v) = le4 v.
Proof. intros v. unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes firstn]. reflexivity. Qed.

Lemma zx32_tnext : forall w, (0 <= w < 2^64)%Z -> zx32 (Z_to_bv 64 w) = Z_to_bv 64 (tnext w).
Proof. intros w Hw. unfold zx32. f_equal. rewrite a_u64_small by lia. rewrite <- land32_tnext by lia. symmetry. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.

Section ArrAt.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.
  Variable d : nat.

  Lemma tape_read_lo32 : forall m (i : Z),
    bytes_at usegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) -> 0 <= i < Z.of_nat (length (ae_tws E)) ->
    ov_read_bytes usegs m (wa (ae_TAPE E + 8 * i)) 4 = Some (le4 (Z_to_bv 64 (Tf (ae_tws E) i))).
  Proof.
    intros m i HB Hi.
    rewrite (bytes_at_read usegs m (ae_TAPE E) _ (8 * i) 4 HB); [| lia| rewrite u64s_length, length_map; lia]. f_equal.
    replace (Z.to_nat (8 * i)) with (8 * Z.to_nat i)%nat by lia.
    match goal with |- firstn 4 ?X = _ => replace (firstn 4 X) with (firstn 4 (firstn 8 X)) by (rewrite firstn_firstn; reflexivity) end.
    rewrite (u64s_read _ (Z.to_nat i)) by (rewrite length_map; lia). rewrite firstn4_le8.
    f_equal. unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
  Qed.

  Lemma arrat_iter : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (e spv : Z)
      (x3 x5 x6 x7 x8 x25 x26 x27 : word),
    bytes_at usegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) ->
    rw_cells usegs m (ae_DOC E) [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))] ->
    e + 1 <= Z.of_nat (length (ae_tws E)) - 1 -> mem_inv usegs m ->
    0 < ae_TAPE E -> ae_TAPE E + 8 * Z.of_nat (length (ae_tws E)) < 2^63 -> ae_TAPE E mod 8 = 0 -> 0 < ae_DOC E -> ae_DOC E + 8 < 2^64 ->
    (forall (it j' : Z) (x1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 x28 x29 x30 x31 : word),
       elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d it j' -> 0 <= it -> j' <= e ->
       evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 (ae_DOC E))
                          xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 it) (Z_to_bv 64 e)
                          (Z_to_bv 64 32) (Z_to_bv 64 4294967295) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x3fa80) fc None m (seg_rom usegs))) ->
    (forall (x1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31 : word),
       evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 (ae_DOC E))
                          xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x3f9d8) fc None m (seg_rom usegs))) ->
    forall (n : nat) (it c' : Z) (x1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 x28 x29 x30 x31 : word),
      tiles (elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d) it e c' -> it <> e -> 0 <= it -> e - it <= Z.of_nat n ->
      evt usegs K (MS (mkR x1 (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 (ae_DOC E))
                         xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 it) (Z_to_bv 64 e)
                         (Z_to_bv 64 32) (Z_to_bv 64 4294967295) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x3fa14) fc None m (seg_rom usegs)).
  Proof.
    intros K m F fc e spv x3 x5 x6 x7 x8 x25 x26 x27 TAPEB DOCC EN MI T0 TN T8 D0 D64 XFOUND XNF.
    pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ _ _ _].
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : Z.of_nat (length (ae_sbs E)) < 2^56) by (destruct WF as (_ & ? & _); lia).
    induction n as [|n IH]; intros it c' x1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 x28 x29 x30 x31 TI NE I0 FUEL.
    { pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TI). lia. }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct (array_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE I0 ltac:(lia)) as (j' & EL & IJ & AFT & TI').

    astep. step. if_cases KF; zify_cond KF.
    { eapply evt_eq; [| eapply (XFOUND it j')]; [atp_st_eq| exact EL| exact I0| lia]. }
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ2.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) HSN) as TIR.
    pose proof (tape_read_type m (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia) TIR) as RDB.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDT.
    assert (TTR : 0 <= ttype (Tf (ae_tws E) it) < 256) by (unfold ttype; lia).

    step. step. step.
    eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := it) (RA := 0x3fa28);
      [exact DOCC| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros ya1 ya2 ya3 ya4.
    astep.

    assert (NEXT : forall (pc xra : Z) (za0 za1 za2 za3 za4 : word), (pc = 0x3fa44 \/ pc = 0x3fa6c \/ pc = 0x3fa78) ->
      evt usegs K (MS (mkR (Z_to_bv 64 xra) (Z_to_bv 64 spv) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 (ae_DOC E))
                         za0 za1 za2 za3 za4 xa5 xa6 xa7 (Z_to_bv 64 (bv_unsigned xs2 + -1)) (Z_to_bv 64 j') (Z_to_bv 64 e)
                         (Z_to_bv 64 32) (Z_to_bv 64 4294967295) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) x25 x26 x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 pc) fc None m (seg_rom usegs))).
    { intros pc xra za0 za1 za2 za3 za4 [-> |[-> | ->]]; (step; if_cases KL; zify_cond KL;
        [ eapply evt_eq; [| eapply (IH j' (c' - 1))]; [atp_st_eq| exact TI'| exact KL| lia| lia]
        | step; eapply evt_eq; [| eapply XNF]; [atp_st_eq] ]). }

    destruct (elem_view_of (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any (fun c cv H => H) HSN d it j' EL I0 ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e2 c2 Ed TY Ej NXT CLOSE TILES|d' e2 c2 Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
    -
      unfold t_true, t_false, t_null in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (astep; step; if_false; astep; astep; step; if_true; astep; astep; step; if_true; astep;
         eapply evt_eq; [| eapply (NEXT 0x3fa78)]; [atp_st_eq| do 2 right; reflexivity]).
    -
      unfold t_i64, t_u64, t_dbl in TY. destruct TY as [TY|[TY|TY]]; rewrite TY;
        (astep; step; if_false; astep; astep; step; if_false; astep;
         eapply evt_eq; [| eapply (NEXT 0x3fa44)]; [atp_st_eq| left; reflexivity]).
    -
      unfold t_str in TY. rewrite TY.
      astep. step. if_true. astep.
      eapply evt_eq; [| eapply (NEXT 0x3fa78)]; [atp_st_eq| do 2 right; reflexivity].
    -
      unfold t_arr in TY. rewrite TY.
      astep. step. if_false. astep. astep. step. if_true. astep. astep. step. if_false.
      step. step. step.
      eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := it) (RA := 0x3fa64);
        [exact DOCC| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
      intros wa1 wa2 wa3 wa4.
      step. astep. rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0x3fa6c)]; [atp_st_eq| right; left; reflexivity].
    -
      unfold t_obj in TY. rewrite TY.
      astep. step. if_false. astep. astep. step. if_true. astep. astep. step. if_false.
      step. step. step.
      eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := it) (RA := 0x3fa64);
        [exact DOCC| lia| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
      intros wa1 wa2 wa3 wa4.
      step. astep. rewrite land32_tnext by lia. rewrite NXT, <- Ej.
      eapply evt_eq; [| eapply (NEXT 0x3fa6c)]; [atp_st_eq| right; left; reflexivity].
  Qed.

  Definition arrat_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo out e : Z) (od : list byte) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (r0 : word) (it code : Z),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(q - 80, q); (out, out + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
      /\ rw_cells usegs m' out [C8 r0; C8 (Z_to_bv 64 it); C4 (Z_to_bv 64 code); CB 4 od]
      /\ ((code = 0 /\ r0 = Z_to_bv 64 (ae_DOC E) /\ 0 <= it /\ exists j', elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d it j' /\ j' <= e)
          \/ (code = 19 /\ r0 = Z_to_bv 64 0 /\ it = 0)).

  Lemma arrat_spec : forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q lo out N2 i e c : Z) (va : word) (oa ob oc od : list byte),
    rw_cells usegs m N2 [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> q <= N2 -> N2 + 16 < 2^63 ->
    bytes_at usegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) ->
    rw_cells usegs m (ae_DOC E) [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))] ->
    ty (Tf (ae_tws E)) i = t_arr -> tnext (Tf (ae_tws E) i) = e + 1 ->
    tiles (elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d) (i + 1) e c ->
    0 <= i -> e + 1 <= Z.of_nat (length (ae_tws E)) - 1 ->
    rw_cells usegs m out [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> q <= out -> out + 24 < 2^63 ->
    RHEAP s (ae_LB E) m -> stk usegs m lo q -> lo <= q - 80 -> ae_lo E <= lo -> mem_inv usegs m -> 0 <= q -> q <= ae_DOC E ->
    evt usegs (arrat_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo out e od m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 N2) va a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATP_ARRAT) fc None m (seg_rom usegs)).
  Proof.
    intros until od. intros N2C QN N63 TAPEB DOCC TY NXT TILES I0 EN OUT QO O63 HEAP ST LO LOLO MI Q0 QD.
    unfold ATP_ARRAT.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [AL8D AL8T]].
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    assert (HSN : Z.of_nat (length (ae_sbs E)) < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (tiles_le _ (elem_lt _ _ _ _ d) _ _ _ TILES) as [IE CC].
    unfold ty in TY. pose proof (ttype_range _ _ TY ltac:(unfold t_arr; lia) ltac:(unfold t_arr; lia)) as TIR.
    pose proof (munch_refl [(q - 80, q); (out, out + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

    hide TAPEB.
    step. carve_frame 80%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 80 junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 10 step. name_mem m1.
    unhide TAPEB.
    assert (TAPEB1 : bytes_at usegs m1 (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E)))).
    { eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact TAPEB|]. rewrite u64s_length, length_map. intros a Ha. cbn [outside]. lia. }
    clear TAPEB. rename TAPEB1 into TAPEB.

    step. step. if_lia. step. astep. rewrite (land7_mod8 (ae_DOC E)) by lia. step. if_false.
    step. step. step. step. step. step.
    eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := i) (RA := 0x3f95c);
      [exact DOCC| lia| lia| lia| lia| exact AL8T| lia| lia| reflexivity| lia| reflexivity|].
    intros ya1 ya2 ya3 ya4.
    pose proof (tape_read_type m1 (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia) TIR) as RDB. rewrite TY in RDB. unfold t_arr in RDB.

    astep. astep. astep. step. if_false. astep. astep. astep. astep. step. if_true.
    astep. astep. astep. astep. astep. step. if_false.

    step. step. if_lia. astep. rewrite (land7_mod8 (ae_DOC E)) by lia. step. if_false. step. step.
    eapply tix_cps with (D := ae_DOC E) (TAPE := ae_TAPE E) (i := i) (RA := 0x3f9bc);
      [exact DOCC| lia| lia| lia| lia| exact AL8T| lia| lia| reflexivity| lia| reflexivity|].
    intros wa1 wa2 wa3 wa4.
    pose proof (tape_read_lo32 m1 i TAPEB ltac:(lia)) as RD4.
    step. rewrite zx32_tnext by lia. rewrite NXT. step.

    astep. astep. replace (e + 1 + -1) with e by lia.

    assert (EPI : forall (x1 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) (m2 : mem) (r0 : word) (it code : Z),
      rw_cells usegs m2 (q + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      mem_inv usegs m2 -> stk usegs m2 lo (q + -80) -> munch [(q - 80, q); (out, out + 24)] m m2 -> wmono usegs m m2 ->
      rw_cells usegs m2 out [C8 r0; C8 (Z_to_bv 64 it); C4 (Z_to_bv 64 code); CB 4 od] ->
      ((code = 0 /\ r0 = Z_to_bv 64 (ae_DOC E) /\ 0 <= it /\ exists j', elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d it j' /\ j' <= e)
          \/ (code = 19 /\ r0 = Z_to_bv 64 0 /\ it = 0)) ->
      evt usegs (arrat_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo out e od m)
        (MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 out) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3fa90) fc None m2 (seg_rom usegs))).
    { intros x1 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 m2 r0 it code EFR EMI EST EMU EWM EOUT ERES.
      do 10 step. step. release_frame EFR EST q. step.
      apply evt_done. unfold arrat_post. do 15 eexists. exists m2, r0, it, code. split; [reflexivity|].
      split; [exact EMU|]. split; [exact EWM|]. split; [exact EMI|]. split; [exact EST|]. split; [exact EOUT| exact ERES]. }
    assert (XNF : forall (x1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 x28 x29 x30 x31 : word),
      evt usegs (arrat_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo out e od m)
        (MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 (ae_DOC E))
                 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3f9d8) fc None m1 (seg_rom usegs))).
    { intros. step. if_lia. astep. hstep. hstep. hstep. step. name_mem m2.
      lazymatch goal with H : rw_cells usegs m2 out _ |- _ => rename H into OUT2 end.
      eapply EPI; [exact FR| assumption| exact ST| exact MU| exact WM| exact OUT2| right; repeat split; reflexivity]. }
    assert (XFOUND : forall (it j' : Z) (x1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 x28 x29 x30 x31 : word),
      elem (Tf (ae_tws E)) (Tf (ae_sbs E)) (Z.of_nat (length (ae_sbs E))) ck_any d it j' -> 0 <= it -> j' <= e ->
      evt usegs (arrat_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo out e od m)
        (MS (mkR x1 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 (ae_DOC E))
                 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 it) (Z_to_bv 64 e)
                 (Z_to_bv 64 32) (Z_to_bv 64 4294967295) (Z_to_bv 64 67240448) (Z_to_bv 64 4294967297) s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x3fa80) fc None m1 (seg_rom usegs))).
    { intros it j' x1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 x28 x29 x30 x31 EL IT0 JE.
      pose proof (elem_lt _ _ _ _ _ _ _ EL).
      step. if_lia. hstep. hstep. hstep. name_mem m2.
      lazymatch goal with H : rw_cells usegs m2 out _ |- _ => rename H into OUT2 end.
      eapply EPI; [exact FR| assumption| exact ST| exact MU| exact WM| exact OUT2| left]. split; [reflexivity|]. split; [reflexivity|]. split; [exact IT0|]. exists j'. split; [exact EL| exact JE]. }
    step. if_cases KE; zify_cond KE.
    -
      do 9 astep.
      eapply evt_eq; [| eapply (arrat_iter (arrat_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo out e od m) m1 F fc e (q + -80)
                                 _ _ _ _ _ _ _ _ TAPEB DOCC EN MI ltac:(lia) ltac:(lia) AL8T ltac:(lia) ltac:(lia) XFOUND XNF
                                 (S (Z.to_nat (e - (i + 1)))) (i + 1) c)];
        [atp_st_eq| exact TILES| exact KE| lia| lia].
    -   apply XNF.
  Qed.
End ArrAt.

End WithCeiling0.
