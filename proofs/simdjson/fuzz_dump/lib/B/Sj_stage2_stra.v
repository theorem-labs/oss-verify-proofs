(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_strkit Sj_stage2_auto Sj_stage2_wkit Sj_stage2_objf Sj_stage2_stram Sj_stage2_strau.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_shadow_dig | s2_load_buf | s2_load_esc | s2_load_dig | s2_load_dig2 | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section StrA.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Section Loop.
    Variables (Q : machine_state -> Prop) (dpt t40 i48 sbv r9 : Z) (sc : list (bool * Z)).
    Hypothesis KX : exit_k E Q.
    Hypothesis HGS : (Z.of_nat (length (e_sbs E)) = sbv)%Z.
    Notation headk := (Sj_stage2_stram.headk E Q dpt t40 i48 sbv sc).
    Notation stra_mb0s := (Sj_stage2_stram.stra_mb0s E OK SHZ Q dpt t40 i48 sbv sc KX HGS).
    Notation stra_mb0p := (Sj_stage2_stram.stra_mb0p E OK SHZ Q dpt t40 i48 sbv sc KX HGS).
    Variables (i j : Z) (kk Wv : Z).
    Hypothesis HROOM : (0 <= sbv /\ sbv + (j - i) + 4 <= e_scap E)%Z.
    Hypothesis HI0 : (0 <= i)%Z.
    Hypothesis H40 : t40 = (e_TAPE E + 8 * Wv)%Z.
    Hypothesis H48 : i48 = (e_IDX E + 4 * kk)%Z.
    Notation stra_u := (Sj_stage2_strau.stra_u E OK SHZ Q dpt t40 i48 sbv sc KX HGS i j HROOM HI0).
    Hypothesis KE : forall d' cb, (0 <= d' <= j - i - 1)%Z -> Z.of_nat (length cb) = d' -> keyend_k (gapp E [] (srec d' cb)) Q kk dpt Wv sbv d' sc.

    Lemma stra_loop : forall (fuel : nat) p d, PS bs i j p d -> (j - p < Z.of_nat fuel)%Z -> headk p d.
    Proof using OK SHZ HROOM HI0 KX HGS KE H40 H48.
      induction fuel as [|fuel IH]; intros p d HPS HF; unfold Sj_stage2_stram.headk; intros xa1 xa2 xa3 xa4 xs2 xs4 xs11 xt6 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j272 j288 j304 F fc m1 HM.
      { pose proof (PS_measure _ _ _ _ _ HPS). lia. }
      pose proof (PS_read _ _ _ _ _ HPS) as (HP0 & HPJ & HJL & HP11).
      pose proof (PS_store _ _ _ _ _ HPS) as (HD0 & HD4).
      pose proof (ok_bytes _ OK) as BOK.
      pose proof (B_range bs p BOK) as HB0.
      s2_env OK.
      pose proof HM as HMo. s2_open_mem HMo.
      wrun.
      if_cases_eq K.
      -
        pose proof (B_range bs (p + 1) BOK) as HB1.
        wrun.
        if_cases_eq K1.
        +
          eapply (stra_u fuel p d HPS K HF IH); wk_close.
        +
          pose proof (esc_range (B bs (p + 1))) as HER.
          wrun.
          if_cases_eq K2.
          *
            wrun_to 0xcd104%Z. gexit KX.
          *
            pose proof (closes_esc_le _ _ _ (ps_closes _ _ _ _ _ HPS) K) as HLE.
            wrun_to 0xbb840%Z.
            replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
            replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
            eapply (IH (p + 2)%Z (d + 1)%Z); [apply PS_esc; [exact HPS | exact K] | lia | eassumption].
      - wrun.
        if_cases_eq K1.
        +
          destruct (PS_quote _ _ _ _ _ HPS ltac:(lia)) as [EJ HDJ].
          wrun_note_to 0xc1d54%Z. s2_str_close d.
          match goal with HMh : MEMI _ _ _ _ _ _ |- _ => rewrite H40 in HMh end.
          rewrite ?H48.
          eapply (KE d _ HDJ SRL). wk_close_ghost.
        +
          wrun_to 0xbb840%Z.
          replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
          replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
          eapply (IH (p + 1)%Z (d + 1)%Z); [apply PS_ord; [exact HPS | lia | lia] | lia | eassumption].
    Qed.
  End Loop.
End StrA.
