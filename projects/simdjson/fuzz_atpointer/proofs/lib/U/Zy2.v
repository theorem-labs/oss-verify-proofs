(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk Zpe Zp9.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Zwd Z103 Zsl Zxc Zxj Zyi Zyj
  Zy4 Zy5 Zy6 Zy7 Zy9 Zyb Zyd Zye Zyf Zyg Zyh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumR.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Hypothesis RLMAX : (blen t <= 1048512)%Z.
  Notation rl := (blen t).
  Hypothesis HSLOWF : slowfu_stmt_g usegs 0x47214 0xb5000.
  Hypothesis HPFF : pffu_stmt_g usegs 0x472c4 0xb5000.
  Hypothesis HROOM : (e_lo E + 368 + NUMU_STACK <= bv_unsigned (e_sp E))%Z.

  Theorem rootnum_walk : forall (Q : machine_state -> Prop),
    Z.of_nat (length (e_tws E)) = 1%Z -> rdel_errA_k E CP Q -> rdel_errB_k E CP Q -> (forall v r, num_word v -> rdel_fin0_k (gapp E [v; r] []) CP Q) -> rdel_fin9_k E CP Q ->
    (forall v r, rdel_fin9_k (gapp E [v; r] []) CP Q) ->
    rootnum_k E CP t Q.
  Proof using OK TOK CP0 CPHI CPSEP RLMAX HSLOWF HPFF HROOM.
    intros Q GLT KXA KXB KF0 KF9 KF9g.
    pose proof (seg_numr_wr E OK CP t TOK CP0 CPHI CPSEP Q GLT KXA KXB KF0 KF9) as KWR.
    pose proof (seg_numr_fb E OK CP t TOK CP0 CPHI CPSEP RLMAX HPFF HROOM Q GLT KXA KXB KF0 KF9 KWR) as KFB.
    pose proof (seg_numr_slow E OK CP t TOK CP0 CPHI CPSEP RLMAX HSLOWF HROOM Q GLT KXA KXB KF0 KF9) as KSLOW.
    pose proof (seg_numr_cmpB E OK CP t TOK CP0 CPHI CPSEP Q KWR KFB) as KCMPB.
    pose proof (seg_numr_zero E OK CP t TOK CP0 CPHI CPSEP Q GLT KXA KXB KF0 KF9) as KZERO.
    pose proof (seg_numr_t33c E OK CP t TOK CP0 CPHI CPSEP Q GLT KXA KXB KF0 KF9 KWR KZERO
                  (fun e He => seg_numr_cmp E OK CP t TOK CP0 CPHI CPSEP Q e He KWR KCMPB)) as K33c.
    assert (TAIL : forall neg, (0 <= neg <= 1)%Z -> (neg < rl)%Z ->
              (forall p e0 x, (0 <= p <= rl)%Z -> (-2097152 <= e0 <= 0)%Z -> (0 <= x < 2^64)%Z -> (x mod 256 = B (crs t) p)%Z ->
                 numr_scan_k E CP t Q neg p e0 x)).
    { intros neg HNEG HS p e0 x HP HE0 HX HXB.
      assert (KFLT : forall x', (0 <= x' < 2^64)%Z -> numr_flt_k E CP t Q neg x')
        by (intros x' Hx'; exact (seg_numr_flt E OK CP t TOK CP0 CPHI CPSEP Q neg x' Hx' HNEG HS K33c KSLOW)).
      assert (KADD : forall w x', (-1000000000000000000 < w < 1000000000000000000)%Z -> (0 <= x' < 2^64)%Z -> numr_eadd_k E CP t Q neg w e0 x')
        by (intros w x' Hw Hx'; exact (seg_numr_eadd E OK CP t TOK CP0 CPHI CPSEP Q neg w e0 x' Hw HE0 Hx' KFLT)).
      assert (KNEG : forall v x', (0 <= v < 10 ^ 18)%Z -> (0 <= x' < 2^64)%Z -> numr_eneg_k E CP t Q neg v e0 x').
      { intros v x' Hv Hx'. change (10 ^ 18)%Z with 1000000000000000000%Z in Hv.
        apply (seg_numr_eneg E OK CP t TOK CP0 CPHI CPSEP Q neg v e0 x' Hv HE0 Hx'). intros w Hw. exact (KADD w x' Hw Hx'). }
      assert (KADDV : forall v x', (0 <= v < 10 ^ 18)%Z -> (0 <= x' < 2^64)%Z -> numr_eadd_k E CP t Q neg v e0 x')
        by (intros v x' Hv Hx'; change (10 ^ 18)%Z with 1000000000000000000%Z in Hv; apply KADD; lia).
      apply (seg_numr_exp E OK CP t TOK CP0 CPHI CPSEP Q neg p e0 x HP HX HXB KFLT).
      - apply (seg_numr_int E OK CP t TOK CP0 CPHI CPSEP Q p HP GLT KXA KXB).
        intros c Hc v r Hv. exact (seg_numr_i468 (gapp E [v; r] []) (env_ok_gapp _ _ _ OK) CP t TOK CP0 CPHI CPSEP Q c Hc (KF0 v r Hv) (KF9g v r)).
      - intros q0 HQ0. apply (seg_numr_e48 E OK CP t TOK CP0 CPHI CPSEP Q neg q0 e0 HQ0 KXA).
        + intros v x' Hv Hx'. exact (seg_numr_e14 E OK CP t TOK CP0 CPHI CPSEP Q neg v e0 x' Hv HE0 Hx' (KNEG v x' Hv Hx') (KADDV v x' Hv Hx')).
        + exact KNEG.
        + exact KADDV. }
    apply (seg_numr_entry E OK CP t TOK CP0 CPHI CPSEP Q KXA).
    - intros neg p HNEG HS HP HDOT.
      assert (HPL : (p < rl)%Z) by (apply Bc_lt; rewrite ?HDOT; lia).
      apply (seg_numr_frac E OK CP t TOK CP0 CPHI CPSEP Q neg p HNEG ltac:(lia)).
      intros d r HD HR HRL.
      apply (seg_numr_ftail E OK CP t TOK CP0 CPHI CPSEP Q neg p d r ltac:(lia) HD HR HRL).
      intros d' x HD' HPD' HX HXB.
      apply (seg_numr_fdig E OK CP t TOK CP0 CPHI CPSEP Q neg p d' x ltac:(lia) ltac:(lia) HPD' HX HXB KXA).
      intros d'' x' HD'' HPD'' HX' HXB'. apply (TAIL neg HNEG HS); [lia | lia | exact HX' | exact HXB'].
    - intros neg p HNEG HS HP.
      pose proof (B_range (crs t) p (crs_bytes_ok t TOK)) as HBP.
      apply (TAIL neg HNEG HS); [lia | lia | lia | apply Z.mod_small; lia].
  Qed.
End NumR.
