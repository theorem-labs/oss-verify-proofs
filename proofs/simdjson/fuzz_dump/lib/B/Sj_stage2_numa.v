(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit2b
  Sj_stage2_numa_defs Sj_stage2_numa_defs2 Sj_stage2_numa_loops
  Sj_stage2_numa1 Sj_stage2_numa2 Sj_stage2_numa3 Sj_stage2_numa3b Sj_stage2_numa4 Sj_stage2_numa4b Sj_stage2_numa5 Sj_stage2_numa6 Sj_stage2_numa7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | s2_load_sown | s2_load_pow | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section NumA.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).

  Theorem seg_numa : forall (Q : machine_state -> Prop) (s : st),
    (0 <= k s <= e_n E)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> (forall v r, exit_k (gapp E [v; r] []) Q) ->
    (forall v r, num_word v -> is_numstart (e_tok E (k s)) = true -> arrcont_k (gapp E [v; r] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    (is_numstart (e_tok E (k s)) = true -> numa_slowcall_k E Q s) ->
    (is_numstart (e_tok E (k s)) = true -> numa_fbcall_k E Q s) ->
    arrnum_k E Q s.
  Proof using OK SHZ.
    intros Q s HK HW0 HW GLT KX KX2 KC KSL KFB.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    pose proof (ok_len _ OK) as HLEN. unfold S2_LEN_MAX in HLEN.
    assert (TAIL : forall neg, is_numstart (e_tok E (k s)) = true -> (0 <= neg <= 1)%Z -> (e_off E (k s) + neg < LEN)%Z ->
              forall p e0, (0 <= p <= LEN)%Z -> (-2097152 <= e0 <= 0)%Z -> numa_scan_k E Q s neg p e0).
    { intros neg HNUM HNEG HS p e0 HP HE0.
      assert (KCC : forall v r, num_word v -> arrcont_k (gapp E [v; r] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) by (intros v r Hv; exact (KC v r Hv HNUM)).
      assert (KFIN : forall v r, num_word v -> numa_fin_k (gapp E [v; r] []) Q s)
        by (intros v r Hv; exact (seg_numa_fin (gapp E [v; r] []) (env_ok_gapp E _ _ OK) SHZ Q s (KX2 v r) (KCC v r Hv))).
      assert (KW : forall ng, numa_write_k E Q s ng) by (intros ng; exact (seg_numa_write E OK SHZ Q s ng HW0 HW GLT KFIN)).
      pose proof (seg_numa_cmpB E OK SHZ Q s neg (KW neg) (KFB HNUM)) as KB.
      pose proof (seg_numa_range E OK SHZ Q s neg HW0 HW GLT KX KCC
                    (fun e He => seg_numa_cmp E OK SHZ Q s neg e He (KW neg) (seg_numa_cmpslow E OK SHZ Q s neg e He (KW neg) KB))) as KR.
      assert (KFLT : forall p', (0 <= p' <= LEN)%Z -> numa_flt_k E Q s neg p')
        by (intros p' HP'; exact (seg_numa_flt E OK SHZ Q s neg p' HK HNEG HS HP' KR (KSL HNUM))).
      apply (seg_numa_scan E OK SHZ Q s neg p e0 HK HNEG HP).
      - intros q0 HQ0.
        assert (KADD : forall p' v, (q0 <= p' <= LEN)%Z -> (-1000000000000000000 < v < 1000000000000000000)%Z -> numa_eadd_k E Q s neg p' e0 v)
          by (intros p' v HP' HV; apply (seg_numa_eadd E OK SHZ Q s neg p' e0 v HE0 HV); apply KFLT; lia).
        apply (seg_numa_expd E OK SHZ Q s neg q0 e0 HK HNEG ltac:(lia) KX).
        + intros p' v HP' HV. change (10 ^ 18)%Z with 1000000000000000000%Z in HV.
          apply (seg_numa_eneg E OK SHZ Q s neg p' e0 v HV). apply KADD; lia.
        + intros p' v HP' HV. change (10 ^ 18)%Z with 1000000000000000000%Z in HV. apply KADD; lia.
      - apply KFLT. exact HP.
      - apply (seg_numa_int E OK SHZ Q s neg p HK HP HW0 HW GLT KX KX2 KCC). }
    apply (seg_numa_entry E OK SHZ Q s HK KX).
    - intros neg p HNUM HNEG HS HP HDOT.
      apply (seg_numa_frac E OK SHZ Q s neg p HK HNEG ltac:(lia)).
      intros d HD HR. apply (seg_numa_ftail E OK SHZ Q s neg p d HK HNEG ltac:(lia) HD HR).
      intros d' HD' HR'. apply (seg_numa_ftail2 E OK SHZ Q s neg p d' HK HNEG ltac:(lia) ltac:(lia) HR' KX).
      intros d'' HD'' HR''. apply (TAIL neg HNUM HNEG HS (p + d'')%Z (1 - d'')%Z); lia.
    - intros neg p HNUM HNEG HS HP. apply (TAIL neg HNUM HNEG HS p 0%Z); lia.
  Qed.

  Theorem seg_numa_after_slow : forall (Q : machine_state -> Prop) (s : st) r v,
    (r = 9 \/ r = 0)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> (forall v' r', exit_k (gapp E [v'; r'] []) Q) ->
    (forall v' r', num_word v' -> arrcont_k (gapp E [v'; r'] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    numa_slowret_k E Q s r v.
  Proof using OK SHZ.
    intros Q s r v HR HW0 HW GLT KX KX2 KC.
    apply (seg_numa_slowret E OK SHZ Q s r v HR HW0 HW GLT KX). intros v' r' Hv.
    exact (seg_numa_fin (gapp E [v'; r'] []) (env_ok_gapp E _ _ OK) SHZ Q s (KX2 v' r') (KC v' r' Hv)).
  Qed.

  Theorem seg_numa_after_fb : forall (Q : machine_state -> Prop) (s : st) r v,
    (r = 0 \/ r = 1)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> (forall v' r', exit_k (gapp E [v'; r'] []) Q) ->
    (forall v' r', num_word v' -> arrcont_k (gapp E [v'; r'] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    numa_fbret_k E Q s r v.
  Proof using OK SHZ.
    intros Q s r v HR HW0 HW GLT KX KX2 KC.
    apply (seg_numa_fbret E OK SHZ Q s r v HR KX).
    apply (seg_numa_write E OK SHZ Q s 0%Z HW0 HW GLT). intros v' r' Hv.
    exact (seg_numa_fin (gapp E [v'; r'] []) (env_ok_gapp E _ _ OK) SHZ Q s (KX2 v' r') (KC v' r' Hv)).
  Qed.
End NumA.
