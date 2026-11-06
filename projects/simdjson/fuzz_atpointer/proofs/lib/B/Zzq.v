(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q ImageA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zpm Zwd Z104 Zwk Z107 Zwm Zzp Zwa Z105 Zzs Zzu.
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

Section StrO.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation INV := (Inv (e_bs E) (e_idxs E)).

  Notation bs := (e_bs E).

  Section Loop.
    Variables (Q : machine_state -> Prop) (dpt t40 i48 sbv r9 : Z) (sc : list (bool * Z)).
    Hypothesis KX : exit_k E Q.
    Hypothesis HGS : (Z.of_nat (length (e_sbs E)) = sbv)%Z.
    Notation headk := (Zzs.headk E Q dpt t40 i48 sbv sc).
    Notation stro_mb0s := (Zzs.stro_mb0s E OK SHZ Q dpt t40 i48 sbv sc KX HGS).
    Notation stro_mb0p := (Zzs.stro_mb0p E OK SHZ Q dpt t40 i48 sbv sc KX HGS).
    Variables (i j : Z) (kk Wv : Z).
    Hypothesis HROOM : (0 <= sbv /\ sbv + (j - i) + 4 <= e_scap E)%Z.
    Hypothesis HI0 : (0 <= i)%Z.
    Hypothesis H40 : t40 = (e_TAPE E + 8 * Wv)%Z.
    Hypothesis H48 : i48 = (e_IDX E + 4 * (kk + 1))%Z.
    Notation stro_u := (Zzu.stro_u E OK SHZ Q dpt t40 i48 sbv sc KX HGS i j HROOM HI0).
    Hypothesis KE : forall d' cb, (0 <= d' <= j - i - 1)%Z -> Z.of_nat (length cb) = d' -> objcont_k (gapp E [] (srec d' cb)) Q (mkst (kk + 1) dpt Wv (sbv + d' + 5) sc).

    Lemma stro_loop : forall (fuel : nat) p d, PS bs i j p d -> (j - p < Z.of_nat fuel)%Z -> headk p d.
    Proof using OK SHZ HROOM HI0 KX HGS KE H40 H48.
      induction fuel as [|fuel IH]; intros p d HPS HF; unfold Zzs.headk; intros xa2 xa3 xa4 xa5 xa6 xs2 xs8 xs11 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j272 j288 j304 F fc m1 HM.
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
          eapply (stro_u fuel p d HPS K HF IH); wk_close.
        +
          pose proof (esc_range (B bs (p + 1))) as HER.
          wrun.
          if_cases_eq K2.
          *
            wrun_to 0xb60c0%Z. gexit KX.
          *
            pose proof (closes_esc_le _ _ _ (ps_closes _ _ _ _ _ HPS) K) as HLE.
            wrun_to 0xab234%Z.
            replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
            replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
            eapply (IH (p + 2)%Z (d + 1)%Z); [apply PS_esc; [exact HPS | exact K] | lia | eassumption].
      - wrun.
        if_cases_eq K1.
        +
          destruct (PS_quote _ _ _ _ _ HPS ltac:(lia)) as [EJ HDJ].
          wrun_note_to 0xb6138%Z. s2_str_close d.
          rewrite ?H40, ?H48.
          eapply (KE d _ HDJ SRL). cbn [scopes k depth W sb]. wk_close_ghost.
        +
          wrun_to 0xab234%Z.
          replace (e_SBUF E + sbv + 4 + d + 1)%Z with (e_SBUF E + sbv + 4 + (d + 1))%Z by lia.
          replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
          eapply (IH (p + 1)%Z (d + 1)%Z); [apply PS_ord; [exact HPS | lia | lia] | lia | eassumption].
    Qed.
  End Loop.
End StrO.
