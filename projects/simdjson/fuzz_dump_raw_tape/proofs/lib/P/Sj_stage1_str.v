(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage1.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage1_defs Sj_stage1_ascii Sj_stage1_utf8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section STR.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma s1_str_loop : forall (Q : machine_state -> Prop) (fs : nat) (i err : Z) (out : list Z)
      xra xt2 xa5 xa6 xs10 xt4 xt5 xt6 (m1 : mem),
    S1INV E m1 out -> (0 <= i < len)%Z -> (len - i <= Z.of_nat fs)%Z ->
    (forall i' err' (u : bool) xt2' xa2' xt3' xt4' xt5' xt6' m1',
       str_loop bs fs i err = (i', err', u) -> S1INV E m1' out ->
       evt psegs Q (S1ST E 0x3cec4 (Z_to_bv 64 err') xt2' xa2' xa5 xa6 (Z_to_bv 64 i') (Z_to_bv 64 (Z.b2z u)) xt3' xt4' xt5' xt6' m1')) ->
    evt psegs Q (S1ST E 0x3cc28 xra xt2 (Z_to_bv 64 err) xa5 xa6 xs10 (Z_to_bv 64 1) (Z_to_bv 64 i) xt4 xt5 xt6 m1).
  Proof using OK.
    intros Q fs. induction fs as [|fs IH]; intros i err out xra xt2 xa5 xa6 xs10 xt4 xt5 xt6 m1 INV Hi Hfs HK; [exfalso; lia|].
    pose proof OK as OK'.
    destruct OK' as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, S1_STACK, S1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    rewrite str_loop_S in HK. rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hi)) in HK. cbv zeta in HK.
    pose proof (ascii_run_bounds bs (length bs) i (proj2 Hi)) as AB.
    set (r := ascii_run bs (length bs) i) in *.

    zstep. s1norm. zstep. zstep. zstep.
    assert (HEAD : evt psegs Q (S1ST E 0x3cc40 (Z_to_bv 64 err) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 len) xa5 xa6 (Z_to_bv 64 i) (Z_to_bv 64 1)
                                 (Z_to_bv 64 i) xt4 xt5 xt6 m1)).
    2:{ if_cases K0; zify_cond K0.
        - zstep. exact HEAD.
        - zstep. zstep. replace (Z_to_bv 64 (i + 1)) with (Z_to_bv 64 len) at 2 by (f_equal; lia). exact HEAD. }
    pose proof INV as INV'. s1_open_inv INV'.
    pose proof (rw_cells_CB_bytes_at _ _ _ _ _ FRtb) as TBL.
    apply (s1_ascii_loop E OK Q (length bs) i); try assumption; try (unfold blen in *; lia).
    -
      intros xt2' Hr TS. fold r in Hr, TS |- *.
      rewrite (proj2 (Z.leb_gt _ _) Hr) in HK.
      pose proof (B_range bs r BOK) as CR. set (b := B bs r) in *.
      pose proof (buf_read m1 (e_BUF E) bs r BUFRO ltac:(lia)) as RD1. fold b in RD1.

      assert (KDE8 : forall i2 err2 xra' xt4' xt5' xt6' m1', (b =? 34)%Z = false -> str_token bs r err = (i2, err2) -> S1INV E m1' out ->
                evt psegs Q (S1ST E 0x3ccdc xra' (Z_to_bv 64 len) (Z_to_bv 64 err2) xa5 xa6 (Z_to_bv 64 r) (Z_to_bv 64 1)
                                  (Z_to_bv 64 i2) xt4' xt5' xt6' m1')).
      { intros i2 err2 xra' xt4' xt5' xt6' m1' NQ ET INV2.
        pose proof (str_token_bounds bs r err) as TB. rewrite NQ in HK. rewrite ET in TB, HK. cbn [fst] in TB.
        zstep. s1norm. zstep.
        if_cases KLT; zify_cond KLT.
        -
          apply (IH i2 err2 out); try assumption; try lia.
        -
          zstep. zstep. zstep. zstep.
          apply (HK i2 err2 true); [|exact INV2].
          apply str_loop_done. lia. }
      zstep. s1norm. zstep. s1norm. zstep.
      if_cases KGE; zify_cond KGE; [exfalso; lia|].
      zstep. s1norm. zstep.
      if_cases K92; zify_cond K92.
      +
        zstep. zstep.
        apply (KDE8 (r + 2)%Z err); [apply Z.eqb_neq; lia| |exact INV].
        unfold str_token. fold b. rewrite (proj2 (Z.eqb_eq _ _) K92). reflexivity.
      + zstep.
        if_cases K34; zify_cond K34.
        *
          rewrite (proj2 (Z.eqb_eq _ _) K34) in HK.
          zstep. zstep. apply (HK r err false); [reflexivity| exact INV].
        * rewrite (proj2 (Z.eqb_neq _ _) K34) in HK.
          zstep. zstep.
          if_cases K80; zify_cond K80.
          --
             pose proof (bit7_set b CR K80) as B80.
             apply (s1_utf8 E OK Q r err out); [exact INV| lia| exact B80|].
             intros xra' xt4' xt5' xt6' m1' INV2.
             apply KDE8; [apply Z.eqb_neq; lia| |exact INV2].
             unfold str_token. fold b. rewrite (proj2 (Z.eqb_neq _ _) K92), (proj2 (Z.leb_le _ _) B80).
             apply surjective_pairing.
          -- pose proof (bit7_clear b CR K80) as B80.
             assert (ETK : str_token bs r err = ((r + 1)%Z, if (b <? 32)%Z then UNESCAPED_CHARS else err)).
             { unfold str_token. fold b. rewrite (proj2 (Z.eqb_neq _ _) K92), (proj2 (Z.leb_gt _ _) B80). reflexivity. }
             zstep.
             if_cases K20; zify_cond K20.
             ++ rewrite (proj2 (Z.ltb_ge _ _) K20) in ETK.
                zstep. zstep. zstep.
                apply (KDE8 (r + 1)%Z err); [apply Z.eqb_neq; lia| exact ETK| exact INV].
             ++ rewrite (proj2 (Z.ltb_lt _ _) K20) in ETK.
                zstep. zstep. zstep. zstep.
                apply (KDE8 (r + 1)%Z UNESCAPED_CHARS); [apply Z.eqb_neq; lia| exact ETK| exact INV].
    -
      intros xt2' xt3' Hr. fold r in Hr.
      assert (X : (len <=? r)%Z = true) by (apply Z.leb_le; lia). rewrite X in HK.
      zstep.
      specialize (HK r err true). rewrite Hr in HK. apply HK; [reflexivity| exact INV].
  Qed.
End STR.
