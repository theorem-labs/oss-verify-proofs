(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem U0FuzzBase U0Fuzz_code FuzzCrcLib FuzzCrcLibU U0Fuzz_crcA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque ctab btab crc_byte.

Definition UKC : list reg := [2; 3; 4; 10]%bv.
Definition UKC2 : list reg := [2; 3; 4; 10; 12]%bv.

Lemma UKC2_UKC : forall regs r, lkeeps UKC2 regs r -> lkeeps UKC regs r.
Proof. intros regs r H. eapply lkeeps_incl; [|exact H]. incl_dec. Qed.
Lemma UKC_UKB : forall regs r, lkeeps UKC regs r -> lkeeps UKB regs r.
Proof. intros regs r H. eapply lkeeps_incl; [|exact H]. incl_dec. Qed.

Section CRCC.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (BA : Z -> Z) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hba : forall a, adr0 <= a < adr0 + len0 -> byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m a = BA a.
  Hypothesis BA_rng : forall a, 0 <= BA a < 256.
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  #[local] Abbreviation WD := (Wd BA).

  Lemma WD_rng : forall a, 0 <= WD a < two32.
  Proof. intros. apply Wd_range. exact BA_rng. Qed.

  Lemma rd4 : forall a, adr0 <= a -> a + 4 <= adr0 + len0 ->
    exists bs, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 a) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (WD a)).
  Proof.
    intros a Ha Ha4. apply (rd4_bytes_at_v (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m a (WD a)); [lia | lia | |].
    - intros i Hi. destruct (Hrd (a + i - adr0) ltac:(lia)) as [b Hb]. exists b.
      replace (adr0 + (a + i - adr0)) with (a + i) in Hb by lia. exact Hb.
    - unfold Wd, wle. rewrite !Hba by lia. reflexivity.
  Qed.

  Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption | solve_kb] ].
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_kb ].
  Ltac notrap F D := stepb_ft F D ltac:(zcond).

  Ltac lw_pl F D Hbs Hv :=
    chain_step;
    [ reflexivity
    | eapply step_lw; [exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
          match type of Hbs with rdn _ _ (Z_to_bv 64 ?y) _ = _ => replace x with y by lia end end;
        exact Hbs
      | exact Hv ]
    | step_simpl; gres; rewrite zv_lw by apply WD_rng ].

  Ltac lw_ctab F D idx :=
    chain_step;
    [ reflexivity
    | eapply step_lw with (v := Z_to_bv 64 (ctab idx));
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with (CTAB + 4 * idx) by (unfold CTAB; lia) end;
        apply rd_ctab; [exact Himg | apply land_255_range]
      | apply ctab_bs_v; apply land_255_range ]
    | step_simpl; gres; rewrite zv_lw by apply ctab_range32 ].

  Ltac lwu_ctab F D idx :=
    chain_step;
    [ reflexivity
    | eapply step_lwu with (v := Z_to_bv 64 (ctab idx));
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with (CTAB + 4 * idx) by (unfold CTAB; lia) end;
        apply rd_ctab; [exact Himg | apply land_255_range]
      | apply ctab_bs_v; apply land_255_range ]
    | step_simpl; gres ].

  Ltac mw1u_step y F1 D1 F2 D2 F3 D3 F4 D4 F5 D5 F6 D6 :=
    stepz F1 D1; stepz F2 D2; stepz F3 D3;
    lw_ctab F4 D4 (Z.land y 255);
    stepz F5 D5; stepz F6 D6;
    change (Z.lxor (sx32 (ctab (Z.land y 255))) (Z.shiftr (y mod two32) 8)) with (mw1u y).

  Lemma ulc1 : forall regs (x0 x1 x2 x3 x4 a : Z),
    getr regs 14 = Z_to_bv 64 x0 -> getr regs 6 = Z_to_bv 64 x1 -> getr regs 17 = Z_to_bv 64 x2 ->
    getr regs 16 = Z_to_bv 64 x3 -> getr regs 15 = Z_to_bv 64 x4 -> getr regs 11 = Z_to_bv 64 a ->
    getr regs 10 = Z_to_bv 64 CTAB ->
    adr0 <= a -> a + 20 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14894 : word) m rom) (mkst r (0x14938 : word) m rom)
      /\ getr r 13 = Z_to_bv 64 (mw4u (mw3u (Z.lxor (sx32 (WD a)) x0)) x1 (WD (a + 4)))
      /\ getr r 17 = Z_to_bv 64 x2 /\ getr r 16 = Z_to_bv 64 x3 /\ getr r 15 = Z_to_bv 64 x4
      /\ getr r 11 = Z_to_bv 64 a /\ getr r 10 = Z_to_bv 64 CTAB
      /\ getr r 28 = Z_to_bv 64 (sx32 (WD (a + 8))) /\ getr r 29 = Z_to_bv 64 (sx32 (WD (a + 12)))
      /\ lkeeps UKC2 regs r.
  Proof.
    intros regs x0 x1 x2 x3 x4 a R14 R6 R17 R16 R15 R11 R10 Ha Ha20.
    destruct (rd4 a ltac:(lia) ltac:(lia)) as (bs0 & Hbs0 & Hv0).
    destruct (rd4 (a + 4) ltac:(lia) ltac:(lia)) as (bs1 & Hbs1 & Hv1).
    destruct (rd4 (a + 8) ltac:(lia) ltac:(lia)) as (bs2 & Hbs2 & Hv2).
    destruct (rd4 (a + 12) ltac:(lia) ltac:(lia)) as (bs3 & Hbs3 & Hv3).
    set (y0 := Z.lxor (sx32 (WD a)) x0).
    eexists. split.
    - stepz F_14834 D_14834. notrap F_14838 D_14838.
      stepz F_1483c D_1483c. notrap F_14840 D_14840.
      stepz F_14844 D_14844. notrap F_14848 D_14848.
      stepz F_1484c D_1484c. notrap F_14850 D_14850.
      stepz F_14854 D_14854. notrap F_14858 D_14858.
      lw_pl F_1485c D_1485c Hbs0 Hv0.
      lw_pl F_14860 D_14860 Hbs1 Hv1.
      lw_pl F_14864 D_14864 Hbs2 Hv2.
      lw_pl F_14868 D_14868 Hbs3 Hv3.
      stepz F_1486c D_1486c. fold y0.
      mw1u_step (y0) F_14870 D_14870 F_14874 D_14874 F_14878 D_14878 F_1487c D_1487c F_14880 D_14880 F_14884 D_14884.
      mw1u_step (mw1u y0) F_14888 D_14888 F_1488c D_1488c F_14890 D_14890 F_14894 D_14894 F_14898 D_14898 F_1489c D_1489c.
      mw1u_step (mw1u (mw1u y0)) F_148a0 D_148a0 F_148a4 D_148a4 F_148a8 D_148a8 F_148ac D_148ac F_148b0 D_148b0 F_148b4 D_148b4.
      change (mw1u (mw1u (mw1u y0))) with (mw3u y0).
      stepz F_148b8 D_148b8. stepz F_148bc D_148bc. stepz F_148c0 D_148c0.
      lw_ctab F_148c4 D_148c4 (Z.land (mw3u y0) 255).
      stepz F_148c8 D_148c8.
      stepz F_148cc D_148cc.
      stepz F_148d0 D_148d0.
      stepz F_148d4 D_148d4.
      change (Z.lxor (Z.lxor (Z.lxor (Z.shiftr (mw3u y0 mod two32) 8) x1) (sx32 (WD (a + 4)))) (sx32 (ctab (Z.land (mw3u y0) 255))))
        with (mw4u (mw3u y0) x1 (WD (a + 4))).
      apply mst_refl.
    - post.
  Qed.

  Lemma ulc2 : forall regs (y1 x2 x3 x4 a : Z),
    getr regs 13 = Z_to_bv 64 y1 -> getr regs 17 = Z_to_bv 64 x2 -> getr regs 16 = Z_to_bv 64 x3 ->
    getr regs 15 = Z_to_bv 64 x4 -> getr regs 11 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 CTAB ->
    getr regs 28 = Z_to_bv 64 (sx32 (WD (a + 8))) -> getr regs 29 = Z_to_bv 64 (sx32 (WD (a + 12))) ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14938 : word) m rom) (mkst r (0x149a0 : word) m rom)
      /\ getr r 13 = Z_to_bv 64 (mw4u (mw3u y1) x2 (WD (a + 8)))
      /\ getr r 16 = Z_to_bv 64 x3 /\ getr r 15 = Z_to_bv 64 x4
      /\ getr r 11 = Z_to_bv 64 a /\ getr r 10 = Z_to_bv 64 CTAB
      /\ getr r 29 = Z_to_bv 64 (sx32 (WD (a + 12)))
      /\ lkeeps UKC2 regs r.
  Proof.
    intros regs y1 x2 x3 x4 a R13 R17 R16 R15 R11 R10 R28 R29.
    eexists. split.
    - mw1u_step (y1) F_148d8 D_148d8 F_148dc D_148dc F_148e0 D_148e0 F_148e4 D_148e4 F_148e8 D_148e8 F_148ec D_148ec.
      mw1u_step (mw1u y1) F_148f0 D_148f0 F_148f4 D_148f4 F_148f8 D_148f8 F_148fc D_148fc F_14900 D_14900 F_14904 D_14904.
      mw1u_step (mw1u (mw1u y1)) F_14908 D_14908 F_1490c D_1490c F_14910 D_14910 F_14914 D_14914 F_14918 D_14918 F_1491c D_1491c.
      change (mw1u (mw1u (mw1u y1))) with (mw3u y1).
      stepz F_14920 D_14920. stepz F_14924 D_14924. stepz F_14928 D_14928.
      lw_ctab F_1492c D_1492c (Z.land (mw3u y1) 255).
      stepz F_14930 D_14930.
      stepz F_14934 D_14934.
      stepz F_14938 D_14938.
      stepz F_1493c D_1493c.
      change (Z.lxor (Z.lxor (Z.lxor (Z.shiftr (mw3u y1 mod two32) 8) x2) (sx32 (WD (a + 8)))) (sx32 (ctab (Z.land (mw3u y1) 255))))
        with (mw4u (mw3u y1) x2 (WD (a + 8))).
      apply mst_refl.
    - post.
  Qed.

  Lemma ulc3 : forall regs (y2 x3 x4 a : Z),
    getr regs 13 = Z_to_bv 64 y2 -> getr regs 16 = Z_to_bv 64 x3 ->
    getr regs 15 = Z_to_bv 64 x4 -> getr regs 11 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 CTAB ->
    getr regs 29 = Z_to_bv 64 (sx32 (WD (a + 12))) ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x149a0 : word) m rom) (mkst r (0x14a08 : word) m rom)
      /\ getr r 13 = Z_to_bv 64 (mw4u (mw3u y2) x3 (WD (a + 12)))
      /\ getr r 15 = Z_to_bv 64 x4
      /\ getr r 11 = Z_to_bv 64 a /\ getr r 10 = Z_to_bv 64 CTAB
      /\ lkeeps UKC2 regs r.
  Proof.
    intros regs y2 x3 x4 a R13 R16 R15 R11 R10 R29.
    eexists. split.
    - mw1u_step (y2) F_14940 D_14940 F_14944 D_14944 F_14948 D_14948 F_1494c D_1494c F_14950 D_14950 F_14954 D_14954.
      mw1u_step (mw1u y2) F_14958 D_14958 F_1495c D_1495c F_14960 D_14960 F_14964 D_14964 F_14968 D_14968 F_1496c D_1496c.
      mw1u_step (mw1u (mw1u y2)) F_14970 D_14970 F_14974 D_14974 F_14978 D_14978 F_1497c D_1497c F_14980 D_14980 F_14984 D_14984.
      change (mw1u (mw1u (mw1u y2))) with (mw3u y2).
      stepz F_14988 D_14988. stepz F_1498c D_1498c. stepz F_14990 D_14990.
      lw_ctab F_14994 D_14994 (Z.land (mw3u y2) 255).
      stepz F_14998 D_14998.
      stepz F_1499c D_1499c.
      stepz F_149a0 D_149a0.
      stepz F_149a4 D_149a4.
      change (Z.lxor (Z.lxor (Z.lxor (Z.shiftr (mw3u y2 mod two32) 8) x3) (sx32 (WD (a + 12)))) (sx32 (ctab (Z.land (mw3u y2) 255))))
        with (mw4u (mw3u y2) x3 (WD (a + 12))).
      apply mst_refl.
    - post.
  Qed.

  Lemma ulc4 : forall regs (y3 x4 a : Z),
    getr regs 13 = Z_to_bv 64 y3 ->
    getr regs 15 = Z_to_bv 64 x4 -> getr regs 11 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 CTAB ->
    adr0 <= a -> a + 20 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14a08 : word) m rom) (mkst r (0x14a74 : word) m rom)
      /\ getr r 13 = Z_to_bv 64 (mw4u (mw3u y3) x4 (WD (a + 16)))
      /\ getr r 11 = Z_to_bv 64 a /\ getr r 10 = Z_to_bv 64 CTAB
      /\ lkeeps UKC2 regs r.
  Proof.
    intros regs y3 x4 a R13 R15 R11 R10 Ha Ha20.
    destruct (rd4 (a + 16) ltac:(lia) ltac:(lia)) as (bs4 & Hbs4 & Hv4).
    eexists. split.
    - mw1u_step (y3) F_149a8 D_149a8 F_149ac D_149ac F_149b0 D_149b0 F_149b4 D_149b4 F_149b8 D_149b8 F_149bc D_149bc.
      mw1u_step (mw1u y3) F_149c0 D_149c0 F_149c4 D_149c4 F_149c8 D_149c8 F_149cc D_149cc F_149d0 D_149d0 F_149d4 D_149d4.
      stepz F_149d8 D_149d8. stepz F_149dc D_149dc. stepz F_149e0 D_149e0.
      lw_ctab F_149e4 D_149e4 (Z.land (mw1u (mw1u y3)) 255).
      lw_pl F_149e8 D_149e8 Hbs4 Hv4.
      stepz F_149ec D_149ec. stepz F_149f0 D_149f0.
      change (Z.lxor (sx32 (ctab (Z.land (mw1u (mw1u y3)) 255))) (Z.shiftr (mw1u (mw1u y3) mod two32) 8)) with (mw3u y3).
      stepz F_149f4 D_149f4. stepz F_149f8 D_149f8. stepz F_149fc D_149fc.
      lw_ctab F_14a00 D_14a00 (Z.land (mw3u y3) 255).
      stepz F_14a04 D_14a04.
      stepz F_14a08 D_14a08.
      stepz F_14a0c D_14a0c.
      stepz F_14a10 D_14a10.
      change (Z.lxor (Z.lxor (Z.lxor (Z.shiftr (mw3u y3 mod two32) 8) x4) (sx32 (WD (a + 16)))) (sx32 (ctab (Z.land (mw3u y3) 255))))
        with (mw4u (mw3u y3) x4 (WD (a + 16))).
      apply mst_refl.
    - post.
  Qed.

  Lemma ulc5 : forall regs (y4 a n q spv : Z),
    getr regs 13 = Z_to_bv 64 y4 -> getr regs 11 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 CTAB ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 spv ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 spv) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 q)) ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14a74 : word) m rom) (mkst r (0x14ae8 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (mwfu (mw3u y4))
      /\ getr r 11 = Z_to_bv 64 (a + 20) /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 12 = Z_to_bv 64 (q * -20 + n)
      /\ lkeeps UKC regs r.
  Proof.
    intros regs y4 a n q spv R13 R11 R10 R12 R2 Hld.
    eexists. split.
    - mw1u_step (y4) F_14a14 D_14a14 F_14a18 D_14a18 F_14a1c D_14a1c F_14a20 D_14a20 F_14a24 D_14a24 F_14a28 D_14a28.
      mw1u_step (mw1u y4) F_14a2c D_14a2c F_14a30 D_14a30 F_14a34 D_14a34 F_14a38 D_14a38 F_14a3c D_14a3c F_14a40 D_14a40.
      stepz F_14a44 D_14a44. stepz F_14a48 D_14a48. stepz F_14a4c D_14a4c.
      lw_ctab F_14a50 D_14a50 (Z.land (mw1u (mw1u y4)) 255).
      stepz F_14a54 D_14a54.
      stepz F_14a58 D_14a58. stepz F_14a5c D_14a5c.
      change (Z.lxor (sx32 (ctab (Z.land (mw1u (mw1u y4)) 255))) (Z.shiftr (mw1u (mw1u y4) mod two32) 8)) with (mw3u y4).
      stepz F_14a60 D_14a60. stepz F_14a64 D_14a64. stepz F_14a68 D_14a68.
      lwu_ctab F_14a6c D_14a6c (Z.land (mw3u y4) 255).
      chain_step;
      [ reflexivity
      | eapply step_ld with (v := Z_to_bv 64 q);
        [ exact F_14a70 | reflexivity | exact D_14a70
        | gres; imm_norm; rwR; rewrite ?zv_addi;
          match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with spv by lia end; exact Hld
        | apply bytes_le_to_Z_8 ]
      | step_simpl; gres ].
      stepz F_14a74 D_14a74.
      stepz F_14a78 D_14a78.
      stepz F_14a7c D_14a7c.
      stepz F_14a80 D_14a80.
      change (Z.lxor (ctab (Z.land (mw3u y4) 255)) (Z.shiftr (mw3u y4 mod two32) 8)) with (mwfu (mw3u y4)).
      stepz F_14a84 D_14a84.
      apply mst_refl.
    - post.
  Qed.

  Lemma ulast_run : forall regs (x : lanes) (a n q spv : Z),
    (let '(x0, x1, x2, x3, x4) := x in
     getr regs 14 = Z_to_bv 64 x0 /\ getr regs 6 = Z_to_bv 64 x1 /\ getr regs 17 = Z_to_bv 64 x2
     /\ getr regs 16 = Z_to_bv 64 x3 /\ getr regs 15 = Z_to_bv 64 x4) ->
    getr regs 11 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 CTAB ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 spv ->
    rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 spv) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 q)) ->
    adr0 <= a -> a + 20 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14894 : word) m rom) (mkst r (0x14ae8 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (mlastx BA x a)
      /\ getr r 11 = Z_to_bv 64 (a + 20) /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 12 = Z_to_bv 64 (q * -20 + n)
      /\ lkeeps UKC regs r.
  Proof.
    intros regs [[[[x0 x1] x2] x3] x4] a n q spv (R14 & R6 & R17 & R16 & R15) R11 R10 R12 R2 Hld Ha Ha20.
    destruct (ulc1 regs x0 x1 x2 x3 x4 a R14 R6 R17 R16 R15 R11 R10 Ha Ha20) as (r1 & M1 & S13 & S17 & S16 & S15 & S11 & S10 & S28 & S29 & K1).
    destruct (ulc2 r1 _ x2 x3 x4 a S13 S17 S16 S15 S11 S10 S28 S29) as (r2 & M2 & T13 & T16 & T15 & T11 & T10 & T29 & K2).
    destruct (ulc3 r2 _ x3 x4 a T13 T16 T15 T11 T10 T29) as (r3 & M3 & U13 & U15 & U11 & U10 & K3).
    destruct (ulc4 r3 _ x4 a U13 U15 U11 U10 Ha Ha20) as (r4 & M4 & V13 & V11 & V10 & K4).
    assert (K14 : lkeeps UKC2 regs r4) by solve_kb.
    assert (V12 : getr r4 12 = Z_to_bv 64 n) by (rewrite (K14 12%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact R12).
    assert (V2 : getr r4 2 = Z_to_bv 64 spv) by (rewrite (K14 2%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact R2).
    destruct (ulc5 r4 _ a n q spv V13 V11 V10 V12 V2 Hld) as (r5 & M5 & W14 & W11 & W10 & W12 & K5).
    exists r5. split; [|split; [|split; [|split; [|split]]]].
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
      eapply msteps_trans; [exact M4 | exact M5].
    - rewrite W14, <- mlastxu_eq. reflexivity.
    - exact W11.
    - exact W10.
    - exact W12.
    - eapply lkeeps_trans; [apply UKC2_UKC; exact K14 | exact K5].
  Qed.
End CRCC.
