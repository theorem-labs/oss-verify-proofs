(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S0FuzzBase S0Fuzz_code FuzzCrcLib S0Fuzz_crcA S0Fuzz_crcB.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque ctab btab crc_byte.
Section FXG. Context {fx : FPState}.

Definition KBC : list reg := [1; 2; 3; 4; 25; 26; 27; 10; 13]%bv.
Definition KBC2 : list reg := [1; 2; 3; 4; 25; 26; 27; 10; 13; 12]%bv.

Lemma KBC2_KBC : forall regs r, lkeeps KBC2 regs r -> lkeeps KBC regs r.
Proof. intros regs r H. eapply lkeeps_incl; [|exact H]. incl_dec. Qed.
Lemma KBC_KB : forall regs r, lkeeps KBC regs r -> lkeeps KB regs r.
Proof. intros regs r H. eapply lkeeps_incl; [|exact H]. incl_dec. Qed.

Section CRCC.
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  #[local] Abbreviation BA := (byte_at RSEGS m).
  #[local] Abbreviation WD := (Wd (byte_at RSEGS m)).

  Lemma WD_rng : forall a, 0 <= WD a < two32.
  Proof. intros. apply Wd_range. intros; apply byte_at_range. Qed.

  Lemma rd4 : forall a, adr0 <= a -> a + 4 <= adr0 + len0 ->
    exists bs, rdn RSEGS m (Z_to_bv 64 a) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (WD a)).
  Proof.
    intros a Ha Ha4. apply (rd4_bytes_at_v RSEGS m a (WD a)); [lia | lia | | reflexivity].
    intros i Hi. destruct (Hrd (a + i - adr0) ltac:(lia)) as [b Hb]. exists b.
    replace (adr0 + (a + i - adr0)) with (a + i) in Hb by lia. exact Hb.
  Qed.

  Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption|]; first [assumption | solve_lkeeps | eapply lkeeps_trans; eassumption] ].
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_kb ].

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

  Ltac mw1_step y F1 D1 F2 D2 F3 D3 F4 D4 F5 D5 F6 D6 :=
    stepz F1 D1; stepz F2 D2; stepz F3 D3;
    lw_ctab F4 D4 (Z.land y 255);
    stepz F5 D5; stepz F6 D6;
    change (Z.lxor (Z.shiftr (y mod two32) 8) (sx32 (ctab (Z.land y 255)))) with (mw1 y).

  Lemma lc1 : forall regs (x0 x1 x2 x3 x4 a : Z),
    getr regs 14 = Z_to_bv 64 x0 -> getr regs 5 = Z_to_bv 64 x1 -> getr regs 17 = Z_to_bv 64 x2 ->
    getr regs 16 = Z_to_bv 64 x3 -> getr regs 15 = Z_to_bv 64 x4 -> getr regs 11 = Z_to_bv 64 a ->
    getr regs 10 = Z_to_bv 64 CTAB ->
    adr0 <= a -> a + 20 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14840 : word) m rom) (mkst r (0x148bc : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (mw4 (mw3 (Z.lxor (sx32 (WD a)) x0)) (Z.lxor x1 (sx32 (WD (a + 4)))))
      /\ getr r 17 = Z_to_bv 64 x2 /\ getr r 16 = Z_to_bv 64 x3 /\ getr r 15 = Z_to_bv 64 x4
      /\ getr r 11 = Z_to_bv 64 a /\ getr r 10 = Z_to_bv 64 CTAB
      /\ getr r 28 = Z_to_bv 64 (sx32 (WD (a + 8))) /\ getr r 29 = Z_to_bv 64 (sx32 (WD (a + 12)))
      /\ lkeeps KBC2 regs r.
  Proof.
    intros regs x0 x1 x2 x3 x4 a R14 R5 R17 R16 R15 R11 R10 Ha Ha20.
    destruct (rd4 a ltac:(lia) ltac:(lia)) as (bs0 & Hbs0 & Hv0).
    destruct (rd4 (a + 4) ltac:(lia) ltac:(lia)) as (bs1 & Hbs1 & Hv1).
    destruct (rd4 (a + 8) ltac:(lia) ltac:(lia)) as (bs2 & Hbs2 & Hv2).
    destruct (rd4 (a + 12) ltac:(lia) ltac:(lia)) as (bs3 & Hbs3 & Hv3).
    set (y0 := Z.lxor (sx32 (WD a)) x0).
    eexists. split.
    - lw_pl F_147e0 D_147e0 Hbs0 Hv0.
      lw_pl F_147e4 D_147e4 Hbs1 Hv1.
      lw_pl F_147e8 D_147e8 Hbs2 Hv2.
      lw_pl F_147ec D_147ec Hbs3 Hv3.
      stepz F_147f0 D_147f0. fold y0.
      mw1_step y0 F_147f4 D_147f4 F_147f8 D_147f8 F_147fc D_147fc F_14800 D_14800 F_14804 D_14804 F_14808 D_14808.
      mw1_step (mw1 y0) F_1480c D_1480c F_14810 D_14810 F_14814 D_14814 F_14818 D_14818 F_1481c D_1481c F_14820 D_14820.
      mw1_step (mw1 (mw1 y0)) F_14824 D_14824 F_14828 D_14828 F_1482c D_1482c F_14830 D_14830 F_14834 D_14834 F_14838 D_14838.
      change (mw1 (mw1 (mw1 y0))) with (mw3 y0).
      stepz F_1483c D_1483c. stepz F_14840 D_14840. stepz F_14844 D_14844.
      lw_ctab F_14848 D_14848 (Z.land (mw3 y0) 255).
      stepz F_1484c D_1484c.
      stepz F_14850 D_14850.
      stepz F_14854 D_14854.
      stepz F_14858 D_14858.
      change (Z.lxor (sx32 (ctab (Z.land (mw3 y0) 255))) (Z.lxor (Z.lxor x1 (sx32 (WD (a + 4)))) (Z.shiftr (mw3 y0 mod two32) 8)))
        with (mw4 (mw3 y0) (Z.lxor x1 (sx32 (WD (a + 4))))).
      apply mst_refl.
    - post.
  Qed.

  Lemma lc2 : forall regs (y1 x2 x3 x4 a : Z),
    getr regs 14 = Z_to_bv 64 y1 -> getr regs 17 = Z_to_bv 64 x2 -> getr regs 16 = Z_to_bv 64 x3 ->
    getr regs 15 = Z_to_bv 64 x4 -> getr regs 11 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 CTAB ->
    getr regs 28 = Z_to_bv 64 (sx32 (WD (a + 8))) -> getr regs 29 = Z_to_bv 64 (sx32 (WD (a + 12))) ->
    exists r, msteps RSEGS (mkst regs (0x148bc : word) m rom) (mkst r (0x14924 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (mw4 (mw3 y1) (Z.lxor x2 (sx32 (WD (a + 8)))))
      /\ getr r 16 = Z_to_bv 64 x3 /\ getr r 15 = Z_to_bv 64 x4
      /\ getr r 11 = Z_to_bv 64 a /\ getr r 10 = Z_to_bv 64 CTAB
      /\ getr r 29 = Z_to_bv 64 (sx32 (WD (a + 12)))
      /\ lkeeps KBC2 regs r.
  Proof.
    intros regs y1 x2 x3 x4 a R14 R17 R16 R15 R11 R10 R28 R29.
    eexists. split.
    - mw1_step y1 F_1485c D_1485c F_14860 D_14860 F_14864 D_14864 F_14868 D_14868 F_1486c D_1486c F_14870 D_14870.
      mw1_step (mw1 y1) F_14874 D_14874 F_14878 D_14878 F_1487c D_1487c F_14880 D_14880 F_14884 D_14884 F_14888 D_14888.
      mw1_step (mw1 (mw1 y1)) F_1488c D_1488c F_14890 D_14890 F_14894 D_14894 F_14898 D_14898 F_1489c D_1489c F_148a0 D_148a0.
      change (mw1 (mw1 (mw1 y1))) with (mw3 y1).
      stepz F_148a4 D_148a4. stepz F_148a8 D_148a8. stepz F_148ac D_148ac.
      lw_ctab F_148b0 D_148b0 (Z.land (mw3 y1) 255).
      stepz F_148b4 D_148b4.
      stepz F_148b8 D_148b8.
      stepz F_148bc D_148bc.
      stepz F_148c0 D_148c0.
      change (Z.lxor (sx32 (ctab (Z.land (mw3 y1) 255))) (Z.lxor (Z.lxor x2 (sx32 (WD (a + 8)))) (Z.shiftr (mw3 y1 mod two32) 8)))
        with (mw4 (mw3 y1) (Z.lxor x2 (sx32 (WD (a + 8))))).
      apply mst_refl.
    - post.
  Qed.

  Lemma lc3 : forall regs (y2 x3 x4 a : Z),
    getr regs 14 = Z_to_bv 64 y2 -> getr regs 16 = Z_to_bv 64 x3 ->
    getr regs 15 = Z_to_bv 64 x4 -> getr regs 11 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 CTAB ->
    getr regs 29 = Z_to_bv 64 (sx32 (WD (a + 12))) ->
    exists r, msteps RSEGS (mkst regs (0x14924 : word) m rom) (mkst r (0x1498c : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (mw4 (mw3 y2) (Z.lxor x3 (sx32 (WD (a + 12)))))
      /\ getr r 15 = Z_to_bv 64 x4
      /\ getr r 11 = Z_to_bv 64 a /\ getr r 10 = Z_to_bv 64 CTAB
      /\ lkeeps KBC2 regs r.
  Proof.
    intros regs y2 x3 x4 a R14 R16 R15 R11 R10 R29.
    eexists. split.
    - mw1_step y2 F_148c4 D_148c4 F_148c8 D_148c8 F_148cc D_148cc F_148d0 D_148d0 F_148d4 D_148d4 F_148d8 D_148d8.
      mw1_step (mw1 y2) F_148dc D_148dc F_148e0 D_148e0 F_148e4 D_148e4 F_148e8 D_148e8 F_148ec D_148ec F_148f0 D_148f0.
      mw1_step (mw1 (mw1 y2)) F_148f4 D_148f4 F_148f8 D_148f8 F_148fc D_148fc F_14900 D_14900 F_14904 D_14904 F_14908 D_14908.
      change (mw1 (mw1 (mw1 y2))) with (mw3 y2).
      stepz F_1490c D_1490c. stepz F_14910 D_14910. stepz F_14914 D_14914.
      lw_ctab F_14918 D_14918 (Z.land (mw3 y2) 255).
      stepz F_1491c D_1491c.
      stepz F_14920 D_14920.
      stepz F_14924 D_14924.
      stepz F_14928 D_14928.
      change (Z.lxor (sx32 (ctab (Z.land (mw3 y2) 255))) (Z.lxor (Z.lxor x3 (sx32 (WD (a + 12)))) (Z.shiftr (mw3 y2 mod two32) 8)))
        with (mw4 (mw3 y2) (Z.lxor x3 (sx32 (WD (a + 12))))).
      apply mst_refl.
    - post.
  Qed.

  Lemma lc4 : forall regs (y3 x4 a : Z),
    getr regs 14 = Z_to_bv 64 y3 ->
    getr regs 15 = Z_to_bv 64 x4 -> getr regs 11 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 CTAB ->
    adr0 <= a -> a + 20 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x1498c : word) m rom) (mkst r (0x149f8 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (mw4 (mw3 y3) (Z.lxor x4 (sx32 (WD (a + 16)))))
      /\ getr r 11 = Z_to_bv 64 a /\ getr r 10 = Z_to_bv 64 CTAB
      /\ lkeeps KBC2 regs r.
  Proof.
    intros regs y3 x4 a R14 R15 R11 R10 Ha Ha20.
    destruct (rd4 (a + 16) ltac:(lia) ltac:(lia)) as (bs4 & Hbs4 & Hv4).
    eexists. split.
    - mw1_step y3 F_1492c D_1492c F_14930 D_14930 F_14934 D_14934 F_14938 D_14938 F_1493c D_1493c F_14940 D_14940.
      mw1_step (mw1 y3) F_14944 D_14944 F_14948 D_14948 F_1494c D_1494c F_14950 D_14950 F_14954 D_14954 F_14958 D_14958.
      stepz F_1495c D_1495c. stepz F_14960 D_14960. stepz F_14964 D_14964.
      lw_ctab F_14968 D_14968 (Z.land (mw1 (mw1 y3)) 255).
      lw_pl F_1496c D_1496c Hbs4 Hv4.
      stepz F_14970 D_14970. stepz F_14974 D_14974.
      change (Z.lxor (Z.shiftr (mw1 (mw1 y3) mod two32) 8) (sx32 (ctab (Z.land (mw1 (mw1 y3)) 255)))) with (mw3 y3).
      stepz F_14978 D_14978. stepz F_1497c D_1497c. stepz F_14980 D_14980.
      lw_ctab F_14984 D_14984 (Z.land (mw3 y3) 255).
      stepz F_14988 D_14988.
      stepz F_1498c D_1498c.
      stepz F_14990 D_14990.
      stepz F_14994 D_14994.
      change (Z.lxor (sx32 (ctab (Z.land (mw3 y3) 255))) (Z.lxor (Z.lxor x4 (sx32 (WD (a + 16)))) (Z.shiftr (mw3 y3 mod two32) 8)))
        with (mw4 (mw3 y3) (Z.lxor x4 (sx32 (WD (a + 16))))).
      apply mst_refl.
    - post.
  Qed.

  Lemma lc5 : forall regs (y4 a n q : Z),
    getr regs 14 = Z_to_bv 64 y4 -> getr regs 11 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 CTAB ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 q ->
    exists r, msteps RSEGS (mkst regs (0x149f8 : word) m rom) (mkst r (0x14a60 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (mwf (mw3 y4))
      /\ getr r 11 = Z_to_bv 64 (a + 20) /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 12 = Z_to_bv 64 (q + n)
      /\ lkeeps KBC regs r.
  Proof.
    intros regs y4 a n q R14 R11 R10 R12 R13.
    eexists. split.
    - mw1_step y4 F_14998 D_14998 F_1499c D_1499c F_149a0 D_149a0 F_149a4 D_149a4 F_149a8 D_149a8 F_149ac D_149ac.
      mw1_step (mw1 y4) F_149b0 D_149b0 F_149b4 D_149b4 F_149b8 D_149b8 F_149bc D_149bc F_149c0 D_149c0 F_149c4 D_149c4.
      mw1_step (mw1 (mw1 y4)) F_149c8 D_149c8 F_149cc D_149cc F_149d0 D_149d0 F_149d4 D_149d4 F_149d8 D_149d8 F_149dc D_149dc.
      change (mw1 (mw1 (mw1 y4))) with (mw3 y4).
      stepz F_149e0 D_149e0. stepz F_149e4 D_149e4. stepz F_149e8 D_149e8.
      lwu_ctab F_149ec D_149ec (Z.land (mw3 y4) 255).
      stepz F_149f0 D_149f0.
      stepz F_149f4 D_149f4.
      stepz F_149f8 D_149f8.
      change (Z.lxor (Z.shiftr (mw3 y4 mod two32) 8) (ctab (Z.land (mw3 y4) 255))) with (mwf (mw3 y4)).
      stepz F_149fc D_149fc.
      apply mst_refl.
    - post.
  Qed.

  Lemma last_run : forall regs (x : lanes) (a n q : Z),
    (let '(x0, x1, x2, x3, x4) := x in
     getr regs 14 = Z_to_bv 64 x0 /\ getr regs 5 = Z_to_bv 64 x1 /\ getr regs 17 = Z_to_bv 64 x2
     /\ getr regs 16 = Z_to_bv 64 x3 /\ getr regs 15 = Z_to_bv 64 x4) ->
    getr regs 11 = Z_to_bv 64 a -> getr regs 10 = Z_to_bv 64 CTAB ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 q ->
    adr0 <= a -> a + 20 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14840 : word) m rom) (mkst r (0x14a60 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (mlastx BA x a)
      /\ getr r 11 = Z_to_bv 64 (a + 20) /\ getr r 10 = Z_to_bv 64 CTAB /\ getr r 12 = Z_to_bv 64 (q + n)
      /\ lkeeps KBC regs r.
  Proof.
    intros regs [[[[x0 x1] x2] x3] x4] a n q (R14 & R5 & R17 & R16 & R15) R11 R10 R12 R13 Ha Ha20.
    destruct (lc1 regs x0 x1 x2 x3 x4 a R14 R5 R17 R16 R15 R11 R10 Ha Ha20) as (r1 & M1 & S14 & S17 & S16 & S15 & S11 & S10 & S28 & S29 & K1).
    destruct (lc2 r1 _ x2 x3 x4 a S14 S17 S16 S15 S11 S10 S28 S29) as (r2 & M2 & T14 & T16 & T15 & T11 & T10 & T29 & K2).
    destruct (lc3 r2 _ x3 x4 a T14 T16 T15 T11 T10 T29) as (r3 & M3 & U14 & U15 & U11 & U10 & K3).
    destruct (lc4 r3 _ x4 a U14 U15 U11 U10 Ha Ha20) as (r4 & M4 & V14 & V11 & V10 & K4).
    assert (K14 : lkeeps KBC2 regs r4).
    { eapply lkeeps_trans; [exact K1|]. eapply lkeeps_trans; [exact K2|]. eapply lkeeps_trans; [exact K3 | exact K4]. }
    assert (V12 : getr r4 12 = Z_to_bv 64 n) by (rewrite (K14 12%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact R12).
    assert (V13 : getr r4 13 = Z_to_bv 64 q) by (rewrite (K14 13%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact R13).
    destruct (lc5 r4 _ a n q V14 V11 V10 V12 V13) as (r5 & M5 & W14 & W11 & W10 & W12 & K5).
    exists r5. split; [|split; [|split; [|split; [|split]]]].
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
      eapply msteps_trans; [exact M4 | exact M5].
    - rewrite W14. reflexivity.
    - exact W11.
    - exact W10.
    - exact W12.
    - eapply lkeeps_trans; [apply KBC2_KBC; exact K14 | exact K5].
  Qed.
End CRCC.
End FXG.
