(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit2b Sj_stage2_numkit3
  Sj_stage2_numr_defs Sj_stage2_numr_defs2 Sj_stage2_numr_defs3 Sj_stage2_numr_loops
  Sj_stage2_numr1 Sj_stage2_numr2 Sj_stage2_numr3 Sj_stage2_numr3b Sj_stage2_numr4 Sj_stage2_numr4b Sj_stage2_numr5 Sj_stage2_numr5b Sj_stage2_numr6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow_cp | s2_load_shadow | s2_load_cp | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section NumR.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).

  Let s0 : st := mkst 0 0 1 0 [].

  Theorem seg_numr : forall (Q : machine_state -> Prop), Z.of_nat (length (e_tws E)) = 1%Z ->
    rdelAc_k E Q CP -> rdelB_k E Q CP -> rdelC_k E Q CP -> (forall v r, num_word v -> rdelC_k (gapp E [v; r] []) Q CP) ->
    numr_slowcall_k E Q CP s0 -> numr_fbcall_k E Q CP s0 ->
    numr_entry_k E Q CP.
  Proof using OK SHZ HCP SHZC.
    intros Q GLT KDA KDB KDC KDC3 KSL KFB.
    assert (GL3 : forall v r, Z.of_nat (length (e_tws (gapp E [v; r] []))) = 3%Z) by (intros; cbn [e_tws gapp s2_ghost]; rewrite length_app; cbn [length]; lia).
    pose proof (seg_numr_delA E OK SHZ CP Q KDA) as KX.
    pose proof (n_bound E OK) as HN. pose proof (ok_tcap _ OK) as [HTC _].
    pose proof (ok_len _ OK) as HLEN. unfold S2_LEN_MAX in HLEN.
    pose proof (off_bound E OK 0 ltac:(lia)) as HO0.
    assert (HRL : (LEN = e_len E - e_off E 0)%Z) by (apply rtxt_blen; lia).
    assert (HK : (0 <= k s0 <= e_n E)%Z) by (cbn; lia).
    assert (KFIN0 : forall v r, num_word v -> numr_fin_k (gapp E [v; r] []) Q CP s0 0 3)
      by (intros v r Hv; exact (seg_numr_fin (gapp E [v; r] []) (env_ok_gapp E _ _ OK) SHZ CP HCP SHZC Q s0 0%Z 3%Z (or_introl eq_refl) (fun _ => eq_refl) (fun _ => GL3 v r) (KDC3 v r Hv))).
    assert (TAIL : forall neg, (0 <= neg <= 1)%Z -> (0 + neg < LEN)%Z -> forall p e0, (0 <= p <= LEN)%Z -> (-2097152 <= e0 <= 0)%Z -> numr_scan_k E Q CP s0 neg p e0).
    { intros neg HNEG HS p e0 HP HE0.
      assert (KW : forall ng, numr_write_k E Q CP s0 ng) by (intros ng; exact (seg_numr_write E OK SHZ CP HCP SHZC Q s0 ng GLT KFIN0)).
      pose proof (seg_numr_cmpB E OK SHZ CP HCP SHZC Q s0 neg (KW neg) KFB) as KB.
      pose proof (seg_numr_range E OK SHZ CP HCP SHZC Q s0 neg GLT KDA KDB KDC3
                    (fun e He => seg_numr_cmp E OK SHZ CP HCP SHZC Q s0 neg e He (KW neg) (seg_numr_cmpslow E OK SHZ CP HCP SHZC Q s0 neg e He (KW neg) KB))) as KR.
      assert (KFLT : forall p', (0 <= p' <= LEN)%Z -> numr_flt_k E Q CP s0 neg p')
        by (intros p' HP'; exact (seg_numr_flt E OK SHZ CP HCP SHZC Q s0 neg p' HK HNEG HS HP' KR KSL)).
      apply (seg_numr_scan E OK SHZ CP HCP SHZC Q s0 neg p e0 HK HNEG HP).
      - intros q0 HQ0.
        assert (KADD : forall p' v, (q0 <= p' <= LEN)%Z -> (-1000000000000000000 < v < 1000000000000000000)%Z -> numr_eadd_k E Q CP s0 neg p' e0 v)
          by (intros p' v HP' HV; apply (seg_numr_eadd E OK SHZ CP HCP SHZC Q s0 neg p' e0 v HE0 HV); apply KFLT; lia).
        apply (seg_numr_expd E OK SHZ CP HCP SHZC Q s0 neg q0 e0 HK HNEG ltac:(lia) KX).
        + intros p' v HP' HV. change (10 ^ 18)%Z with 1000000000000000000%Z in HV.
          apply (seg_numr_eneg E OK SHZ CP HCP SHZC Q s0 neg p' e0 v HV). apply KADD; lia.
        + intros p' v HP' HV. change (10 ^ 18)%Z with 1000000000000000000%Z in HV. apply KADD; lia.
      - apply KFLT. exact HP.
      - apply (seg_numr_int E OK SHZ CP HCP SHZC Q s0 neg p HP GLT KDA KDB KDC KDC3). }
    apply (seg_numr_entry E OK SHZ CP HCP SHZC Q s0 KX).
    - intros neg p HNEG HS HP HDOT.
      apply (seg_numr_frac E OK SHZ CP HCP SHZC Q s0 neg p HK HNEG ltac:(lia)).
      intros d HD HR. apply (seg_numr_ftail E OK SHZ CP HCP SHZC Q s0 neg p d HK HNEG ltac:(lia) HD HR).
      intros d' HD' HR'. apply (seg_numr_ftail2 E OK SHZ CP HCP SHZC Q s0 neg p d' HK HNEG ltac:(lia) ltac:(lia) HR' KX).
      intros d'' HD'' HR''. apply (TAIL neg HNEG HS (p + d'')%Z (1 - d'')%Z); lia.
    - intros neg p HNEG HS HP. apply (TAIL neg HNEG HS p 0%Z); lia.
  Qed.

  Theorem seg_numr_after_slow : forall (Q : machine_state -> Prop) r v,
    (r = 9 \/ r = 0)%Z -> Z.of_nat (length (e_tws E)) = 1%Z -> (forall v' r', num_word v' -> rdelC_k (gapp E [v'; r'] []) Q CP) -> numr_slowret_k E Q CP s0 r v.
  Proof using OK SHZ HCP SHZC.
    intros Q r v HR GLT KDC3.
    apply (seg_numr_slowret E OK SHZ CP HCP SHZC Q s0 r v HR GLT). intros v' r' Hv.
    apply (seg_numr_fin (gapp E [v'; r'] []) (env_ok_gapp E _ _ OK) SHZ CP HCP SHZC Q s0 r 3%Z ltac:(destruct HR; [right | left]; assumption) (fun _ => eq_refl)
             ltac:(intros _; cbn [e_tws gapp s2_ghost]; rewrite length_app; cbn [length]; lia) (KDC3 v' r' Hv)).
  Qed.
  Theorem seg_numr_after_fb : forall (Q : machine_state -> Prop) r v,
    (r = 0 \/ r = 1)%Z -> Z.of_nat (length (e_tws E)) = 1%Z -> rdelC_k E Q CP -> (forall v' r', num_word v' -> rdelC_k (gapp E [v'; r'] []) Q CP) -> numr_fbret_k E Q CP s0 r v.
  Proof using OK SHZ HCP SHZC.
    intros Q r v HR GLT KDC KDC3.
    apply (seg_numr_fbret E OK SHZ CP HCP SHZC Q s0 r v HR).
    - apply (seg_numr_fin E OK SHZ CP HCP SHZC Q s0 9%Z 1%Z (or_intror eq_refl) ltac:(intros HH; discriminate HH) ltac:(intros HH; discriminate HH) KDC).
    - apply (seg_numr_write E OK SHZ CP HCP SHZC Q s0 0%Z GLT). intros v' r' Hv.
      apply (seg_numr_fin (gapp E [v'; r'] []) (env_ok_gapp E _ _ OK) SHZ CP HCP SHZC Q s0 0%Z 3%Z (or_introl eq_refl) (fun _ => eq_refl)
             ltac:(intros _; cbn [e_tws gapp s2_ghost]; rewrite length_app; cbn [length]; lia) (KDC3 v' r' Hv)).
  Qed.
End NumR.
