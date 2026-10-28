(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage1_defs Sj_stage1_ascii Sj_stage1_utf8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section STR.
  Variable E : s1env.
  Hypothesis OK : env_ok_u E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma u1_str_loop : forall (Q : machine_state -> Prop) (fs : nat) (i err : Z) (out : list Z) xa0 xa5 xs3 xt3 xt5 xt6 (m1 : mem),
    U1INV E m1 out i err -> (0 <= i < len)%Z -> (len - i <= Z.of_nat fs)%Z ->
    (forall i' err' (u : bool) idxc' xra' xa5' xt5' xt6' m1',
       str_loop bs fs i err = (i', err', u) -> U1INV E m1' out idxc' err' ->
       evt usegs Q (U1ST E 0x41b14 xra' xa0 (Z_to_bv 64 (Z.b2z u)) xa5' (Z_to_bv 64 i') (Z_to_bv 64 len) xt3 xt5' xt6' m1')) ->
    evt usegs Q (U1ST E 0x41bdc (Z_to_bv 64 i) xa0 (Z_to_bv 64 1) xa5 xs3 (Z_to_bv 64 len) xt3 xt5 xt6 m1).
  Proof using OK.
    intros Q fs. induction fs as [|fs IH]; intros i err out xa0 xa5 xs3 xt3 xt5 xt6 m1 INV Hi Hfs HK; [exfalso; lia|].
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    rewrite str_loop_S in HK. rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hi)) in HK. cbv zeta in HK.
    pose proof (ascii_run_bounds bs (length bs) i (proj2 Hi)) as AB.
    set (r := ascii_run bs (length bs) i) in *.
    apply (u1_ascii_loop E OK Q (length bs) i out err); try assumption; try (unfold blen in *; lia).
    -
      intros xa5' xt5' m1' Hr TS INV1. fold r in Hr, TS, INV1 |- *.
      rewrite (proj2 (Z.leb_gt _ _) Hr) in HK.
      pose proof (B_range bs r BOK) as CR. set (b := B bs r) in *.

      assert (KE88 : forall i2 err2 idxc' xa5'' xt5'' xt6'' m2, (b =? 34)%Z = false -> str_token bs r err = (i2, err2) -> U1INV E m2 out idxc' err2 ->
                evt usegs Q (U1ST E 0x41bd4 (Z_to_bv 64 i2) xa0 (Z_to_bv 64 1) xa5'' (Z_to_bv 64 r) (Z_to_bv 64 len) xt3 xt5'' xt6'' m2)).
      { intros i2 err2 idxc' xa5'' xt5'' xt6'' m2 NQ ET INV2.
        pose proof (str_token_bounds bs r err) as TB. rewrite NQ in HK. rewrite ET in TB, HK. cbn [fst] in TB.
        u1_open_inv INV2.
        zstep. zstep.
        assert (INV3 : U1INV E m out i2 err2) by u1_close_inv.
        if_cases KGE; zify_cond KGE.
        -
          zstep.
          apply (HK i2 err2 true i2); [apply str_loop_done; lia| exact INV3].
        - apply (IH i2 err2 out); try assumption; try lia. }
      pose proof INV1 as INV1'. u1_open_inv INV1'.
      pose proof (ubuf_read m1' (e_BUF E) bs r BUFRO ltac:(lia)) as RD1. fold b in RD1.
      zstep. zstep. s1norm. zstep. zstep.
      if_cases G1; zify_cond G1; [|exfalso; lia].
      zstep. s1norm. zstep.
      if_cases K92; zify_cond K92.
      +
        zstep. s1norm.
        apply (KE88 (r + 2)%Z err r); [apply Z.eqb_neq; lia| |exact INV1].
        unfold str_token. fold b. rewrite (proj2 (Z.eqb_eq _ _) K92). reflexivity.
      + zstep.
        if_cases K34; zify_cond K34.
        *
          rewrite (proj2 (Z.eqb_eq _ _) K34) in HK.
          zstep. zstep. apply (HK r err false r); [reflexivity| exact INV1].
        * rewrite (proj2 (Z.eqb_neq _ _) K34) in HK.
          zstep. zstep.
          if_cases K80; zify_cond K80.
          --
             pose proof (bit7_set b CR K80) as B80.
             replace (Z_to_bv 64 (r + e_BUF E)) with (Z_to_bv 64 (r + e_BUF E)) by reflexivity.
             apply (u1_utf8 E OK Q r err out r); [exact INV1| lia| exact B80|].
             intros xa5'' xt5'' m2 INV2.
             eapply (KE88 _ _ r); [apply Z.eqb_neq; lia| |exact INV2].
             unfold str_token. fold b. rewrite (proj2 (Z.eqb_neq _ _) K92), (proj2 (Z.leb_le _ _) B80).
             apply surjective_pairing.
          -- pose proof (bit7_clear b CR K80) as B80.
             assert (ETK : str_token bs r err = ((r + 1)%Z, if (b <? 32)%Z then UNESCAPED_CHARS else err)).
             { unfold str_token. fold b. rewrite (proj2 (Z.eqb_neq _ _) K92), (proj2 (Z.leb_gt _ _) B80). reflexivity. }
             zstep.
             if_cases K20; zify_cond K20.
             ++ assert (X : (b <? 32)%Z = false) by (apply Z.ltb_ge; lia). rewrite X in ETK.
                zstep. s1norm. zstep.
                apply (KE88 (r + 1)%Z err r); [apply Z.eqb_neq; lia| exact ETK| exact INV1].
             ++ assert (X : (b <? 32)%Z = true) by (apply Z.ltb_lt; lia). rewrite X in ETK.
                zstep. zstep. s1norm. zstep.
                apply (KE88 (r + 1)%Z UNESCAPED_CHARS r); [apply Z.eqb_neq; lia| exact ETK| unfold UNESCAPED_CHARS; u1_close_inv].
    -
      intros xa5' xt5' m1' Hr INV1. fold r in Hr.
      assert (X : (len <=? r)%Z = true) by (apply Z.leb_le; lia). rewrite X in HK.
      specialize (HK r err true len). rewrite Hr in HK. apply HK; [reflexivity| exact INV1].
  Qed.
End STR.
