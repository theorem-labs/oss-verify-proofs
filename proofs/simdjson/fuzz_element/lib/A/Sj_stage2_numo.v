(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numo_defs Sj_stage2_numo_defs2
  Sj_stage2_numo1 Sj_stage2_numo2 Sj_stage2_numo3 Sj_stage2_numo4 Sj_stage2_numo5 Sj_stage2_numo6 Sj_stage2_numo7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumO.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).

  Theorem seg_numo : forall (Q : machine_state -> Prop) (s : st),
    (0 <= k s <= e_n E)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> (forall v r, exit_k (gapp E [v; r] []) Q) ->
    (forall v r, num_word v -> is_numstart (e_tok E (k s)) = true -> objcont_k (gapp E [v; r] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    (is_numstart (e_tok E (k s)) = true -> numo_slowcall_k E Q s) ->
    (is_numstart (e_tok E (k s)) = true -> numo_fbcall_k E Q s) ->
    objnum_k E Q s.
  Proof using OK SHZ.
    intros Q s HK HW0 HW GLT KX KX2 KC KSL KFB.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    assert (TAIL : forall neg, is_numstart (e_tok E (k s)) = true -> (0 <= neg <= 1)%Z -> (e_off E (k s) + neg < LEN)%Z ->
              forall p, (0 <= p <= LEN)%Z -> numo_scan_k E Q s neg p).
    { intros neg HNUM HNEG HS p HP.
      assert (KJ : forall v r, num_word v -> numo_join_k (gapp E [v; r] []) Q s)
        by (intros v r Hv; exact (seg_numo_join (gapp E [v; r] []) (env_ok_gapp E _ _ OK) SHZ Q s (KC v r Hv HNUM))).
      assert (KFIN0 : forall v r, num_word v -> numo_fin_k (gapp E [v; r] []) Q s neg 0)
        by (intros v r Hv; exact (seg_numo_fin (gapp E [v; r] []) (env_ok_gapp E _ _ OK) SHZ Q s neg 0%Z (or_introl eq_refl) (KX2 v r) (KJ v r Hv))).
      pose proof (seg_numo_write E OK SHZ Q s neg HW0 HW GLT KFIN0) as KW.
      pose proof (seg_numo_range E OK SHZ Q s neg HW0 HW GLT KX KJ (fun e He => seg_numo_cmp E OK SHZ Q s neg e He KW (seg_numo_cmpslow E OK SHZ Q s neg e He KW (KFB HNUM)))) as KR.
      assert (KFLT : forall p', (0 <= p' <= LEN)%Z -> numo_flt_k E Q s neg p')
        by (intros p' HP'; exact (seg_numo_flt E OK SHZ Q s neg p' HK HNEG HS HP' KR (KSL HNUM))).
      apply (seg_numo_scan E OK SHZ Q s neg p HK HNEG HP).
      - intros q0 HQ0. apply (seg_numo_expd E OK SHZ Q s neg q0 HK HNEG ltac:(lia) KX). intros p' HP'. apply KFLT. lia.
      - apply KFLT. exact HP.
      - apply (seg_numo_int E OK SHZ Q s neg p HK HP HW0 HW GLT KX KJ). }
    apply (seg_numo_entry E OK SHZ Q s HK KX).
    intros neg p HNUM HNEG HS HP.
    apply (seg_numo_dot E OK SHZ Q s neg p HK HNEG HP).
    - intros HDOT.
      assert (HPL : (p < LEN)%Z) by (nz_lt_by ltac:(rewrite HDOT; lia)).
      apply (seg_numo_frac E OK SHZ Q s neg p HK HNEG ltac:(lia)).
      intros r HR. apply (seg_numo_ftail E OK SHZ Q s neg p r HK HNEG ltac:(lia) HR).
      intros r' HR'. apply (seg_numo_ftail2 E OK SHZ Q s neg p r' HK HNEG ltac:(lia) ltac:(lia) KX).
      intros p' HP'. apply (TAIL neg HNUM HNEG HS p'). lia.
    - apply (TAIL neg HNUM HNEG HS p). lia.
  Qed.

  Theorem seg_numo_after_slow : forall (Q : machine_state -> Prop) (s : st) r v,
    (r = 9 \/ r = 0)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> (forall v' r', exit_k (gapp E [v'; r'] []) Q) ->
    (forall v' r', num_word v' -> objcont_k (gapp E [v'; r'] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    numo_slowret_k E Q s r v.
  Proof using OK SHZ.
    intros Q s r v HR HW0 HW GLT KX2 KC.
    apply (seg_numo_slowret E OK SHZ Q s r v HW0 HW GLT). intros v' r' Hv.
    apply (seg_numo_fin (gapp E [v'; r'] []) (env_ok_gapp E _ _ OK) SHZ Q s 0%Z r ltac:(destruct HR; [right | left]; assumption) (KX2 v' r')).
    exact (seg_numo_join (gapp E [v'; r'] []) (env_ok_gapp E _ _ OK) SHZ Q s (KC v' r' Hv)).
  Qed.

  Theorem seg_numo_after_fb : forall (Q : machine_state -> Prop) (s : st) r v,
    (r = 0 \/ r = 1)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> (forall v' r', exit_k (gapp E [v'; r'] []) Q) ->
    (forall v' r', num_word v' -> objcont_k (gapp E [v'; r'] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    numo_fbret_k E Q s r v.
  Proof using OK SHZ.
    intros Q s r v HR HW0 HW GLT KX KX2 KC.
    apply (seg_numo_fbret E OK SHZ Q s r v HR KX).
    apply (seg_numo_write E OK SHZ Q s 0%Z HW0 HW GLT). intros v' r' Hv.
    apply (seg_numo_fin (gapp E [v'; r'] []) (env_ok_gapp E _ _ OK) SHZ Q s 0%Z 0%Z (or_introl eq_refl) (KX2 v' r')).
    exact (seg_numo_join (gapp E [v'; r'] []) (env_ok_gapp E _ _ OK) SHZ Q s (KC v' r' Hv)).
  Qed.
End NumO.
