(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_stage1_defs Sj_stage1_ascii Sj_stage1_utf8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section STR.
  Variable E : s1env.
  Hypothesis OK : env_ok_b E.
  Hypothesis SHZ : b1_shz E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma b1_str_loop : forall (Q : machine_state -> Prop) (fs : nat) (i err : Z) (out : list Z) xa1 xa2 xa3 xs6 xt5 (m1 : mem),
    B1INV E m1 out i err -> (0 <= i < len)%Z -> (len - i <= Z.of_nat fs)%Z ->
    (forall i' err' (u : bool) xa2' xs5' xs6' xt5' xt6' m1',
       str_loop bs fs i err = (i', err', u) -> B1INV E m1' out i' err' ->
       evt bsegs Q (B1ST E 0xb34bc xa1 xa2' xa3 (Z_to_bv 64 (Z.b2z u)) xs5' xs6' xt5' xt6' m1')) ->
    evt bsegs Q (B1ST E 0xb35d4 xa1 xa2 xa3 (Z_to_bv 64 1) (Z_to_bv 64 i) xs6 xt5 (Z_to_bv 64 len) m1).
  Proof using OK SHZ.
    intros Q fs. induction fs as [|fs IH]; intros i err out xa1 xa2 xa3 xs6 xt5 m1 INV Hi Hfs HK; [exfalso; lia|].
    pose proof OK as OK'.
    destruct OK' as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, B1_STACK, B1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    rewrite str_loop_S in HK. rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hi)) in HK. cbv zeta in HK.
    pose proof (ascii_run_bounds bs (length bs) i (proj2 Hi)) as AB.
    set (r := ascii_run bs (length bs) i) in *.
    apply (b1_ascii_loop E OK SHZ Q (length bs) i out err); try assumption; try (unfold blen in *; lia).
    intros xa2' xt5' m1' INV1. fold r in INV1 |- *.
    zstep.
    if_cases KR; zify_cond KR.
    -
      assert (X : (len <=? r)%Z = true) by (apply Z.leb_le; lia). rewrite X in HK.
      apply (HK r err true); [reflexivity| exact INV1].
    -
      assert (Hr : (r < len)%Z) by lia.
      rewrite (proj2 (Z.leb_gt _ _) Hr) in HK.
      pose proof (B_range bs r BOK) as CR. set (b := B bs r) in *.

      assert (K548 : forall i2 err2 xs5'' xs6'' xt5'' m2, (b =? 34)%Z = false -> str_token bs r err = (i2, err2) -> B1INV E m2 out r err2 ->
                evt bsegs Q (B1ST E 0xb35c8 xa1 (Z_to_bv 64 i2) xa3 (Z_to_bv 64 1) xs5'' xs6'' xt5'' (Z_to_bv 64 len) m2)).
      { intros i2 err2 xs5'' xs6'' xt5'' m2 NQ ET INV2.
        pose proof (str_token_bounds bs r err) as TB. rewrite NQ in HK. rewrite ET in TB, HK. cbn [fst] in TB.
        b1_open_inv INV2.
        zstep. zstep.
        s1_cur_mem ltac:(fun mm => assert (INV3 : B1INV E mm out i2 err2) by b1_close_inv).
        zstep.
        if_cases KGE; zify_cond KGE.
        -
          apply (HK i2 err2 true); [apply str_loop_done; lia| exact INV3].
        - apply (IH i2 err2 out); try assumption; try lia. }
      pose proof INV1 as INV1'. b1_open_inv INV1'.
      pose proof (buf_read m1' (e_BUF E) bs r BUFRO ltac:(lia)) as RD1. fold b in RD1.
      zstep. zstep. s1norm. zstep. zstep.
      if_cases G1; zify_cond G1; [|exfalso; lia].
      b1_shz_buf SHZ (r + e_BUF E)%Z.
      zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_false.
      zstep. s1norm. zstep.
      if_cases K92; zify_cond K92.
      +
        zstep. s1norm.
        apply (K548 (r + 2)%Z err); [apply Z.eqb_neq; lia| |exact INV1].
        unfold str_token. fold b. rewrite (proj2 (Z.eqb_eq _ _) K92). reflexivity.
      + zstep.
        if_cases K34; zify_cond K34.
        *
          rewrite (proj2 (Z.eqb_eq _ _) K34) in HK.
          zstep. apply (HK r err false); [reflexivity| exact INV1].
        * rewrite (proj2 (Z.eqb_neq _ _) K34) in HK.
          zstep. zstep.
          if_cases K80; zify_cond K80.
          --
             pose proof (bit7_set b CR K80) as B80.
             apply (b1_utf8 E OK SHZ Q r err out); [exact INV1| lia| exact B80|].
             intros xs6'' xt5'' m2 INV2.
             eapply (K548 _ _); [apply Z.eqb_neq; lia| |exact INV2].
             unfold str_token. fold b. rewrite (proj2 (Z.eqb_neq _ _) K92), (proj2 (Z.leb_le _ _) B80).
             apply surjective_pairing.
          -- pose proof (bit7_clear b CR K80) as B80.
             assert (ETK : str_token bs r err = ((r + 1)%Z, if (b <? 32)%Z then UNESCAPED_CHARS else err)).
             { unfold str_token. fold b. rewrite (proj2 (Z.eqb_neq _ _) K92), (proj2 (Z.leb_gt _ _) B80). reflexivity. }
             zstep.
             if_cases K20; zify_cond K20.
             ++ assert (X : (b <? 32)%Z = false) by (apply Z.ltb_ge; lia). rewrite X in ETK.
                zstep. s1norm. zstep.
                apply (K548 (r + 1)%Z err); [apply Z.eqb_neq; lia| exact ETK| exact INV1].
             ++ assert (X : (b <? 32)%Z = true) by (apply Z.ltb_lt; lia). rewrite X in ETK.
                zstep. zstep. s1norm. zstep.
                apply (K548 (r + 1)%Z UNESCAPED_CHARS); [apply Z.eqb_neq; lia| exact ETK| unfold UNESCAPED_CHARS; b1_close_inv].
  Qed.
End STR.
