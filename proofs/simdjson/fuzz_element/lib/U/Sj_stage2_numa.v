(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjNumber SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_num_iface Sj_stage2_numkit Sj_stage2_numa_defs Sj_stage2_numa_defs2
  Sj_stage2_numa1 Sj_stage2_numa2 Sj_stage2_numa2b Sj_stage2_numa3 Sj_stage2_numa4 Sj_stage2_numa5 Sj_stage2_numa6 Sj_stage2_numa7 Sj_stage2_numa8 Sj_stage2_numa9.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section NumA.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Hypothesis HSLOWF : slowfu_stmt_g usegs 0x5edf4 0x111000.
  Hypothesis HPFF : pffu_stmt_g usegs 0x5eea4 0x111000.
  Hypothesis HROOM : (e_lo E + 368 + NUMU_STACK <= bv_unsigned (e_sp E))%Z.

  Theorem seg_numa : forall (Q : machine_state -> Prop) (s : st),
    (0 <= k s <= e_n E)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v r, num_word v -> is_numstart (e_tok E (k s)) = true -> arrcont_k (gapp E [v; r] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    arrnum_k E Q s.
  Proof using OK HSLOWF HPFF HROOM.
    intros Q s HK HW0 HW GLT KX KC.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    pose proof (ok_len _ OK) as HLEN. unfold S2_LEN_MAX in HLEN.
    assert (TAIL : forall neg, is_numstart (e_tok E (k s)) = true -> (0 <= neg <= 1)%Z -> (e_off E (k s) + neg < e_len E)%Z ->
              (forall p e0 x, (0 <= p <= e_len E)%Z -> (-2097152 <= e0 <= 0)%Z -> (0 <= x < 2^64)%Z -> (x mod 256 = B bs p)%Z ->
                 numa_scan_k E Q s neg p e0 x)).
    { intros neg HNUM HNEG HS p e0 x HP HE0 HX HXB.
      assert (KCC : forall v r, num_word v -> arrcont_k (gapp E [v; r] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) by (intros v r Hv; exact (KC v r Hv HNUM)).
      pose proof (seg_numa_wr34 E OK Q s neg HW0 HW GLT KX KCC) as KWR34.
      pose proof (seg_numa_wr30 E OK Q s neg HW0 HW GLT KX KCC) as KWR30.
      pose proof (seg_numa_fb E OK HPFF HROOM Q s neg HK KX KWR30) as KFB.
      pose proof (seg_numa_slow E OK HSLOWF HROOM Q s neg HK HW0 HW GLT KX KCC) as KSLOW.
      pose proof (seg_numa_cmpB E OK Q s neg KWR30 KFB) as KCMPB.
      pose proof (seg_numa_tac0 E OK Q s neg HW0 HW GLT KX KCC KWR34 (fun e He => seg_numa_cmp E OK Q s neg e He KWR30 KCMPB)) as KAC0.
      assert (KFLT : forall x', (0 <= x' < 2^64)%Z -> numa_flt_k E Q s neg x')
        by (intros x' Hx'; exact (seg_numa_flt E OK Q s neg x' Hx' HNEG HK HS KAC0 KSLOW)).
      apply (seg_numa_exp E OK Q s neg p e0 x HP HX HXB KFLT).
      - exact (seg_numa_int E OK Q s neg p HP HW0 HW GLT KX KCC).
      - intros q0 HQ0. apply (seg_numa_e48 E OK Q s neg q0 e0 HQ0 KX).
        intros v x' Hv Hx'. exact (seg_numa_e14 E OK Q s neg v e0 x' Hv HE0 Hx' KFLT). }
    apply (seg_numa_entry E OK Q s HK KX).
    - intros neg p HNUM HNEG HS HP HDOT.
      assert (HPL : (p < e_len E)%Z) by (apply B_nz_lt; rewrite HDOT; lia).
      apply (seg_numa_frac E OK Q s neg p HK HNEG ltac:(lia)).
      intros d r HD HR HRL.
      apply (seg_numa_ftail E OK Q s neg p d r ltac:(lia) HD HR HRL).
      intros d' x HD' HPD' HX HXB.
      apply (seg_numa_fdig E OK Q s neg p d' x ltac:(lia) ltac:(lia) HPD' HX HXB KX).
      intros d'' x' HD'' HPD'' HX' HXB'. apply (TAIL neg HNUM HNEG HS); [lia | lia | exact HX' | exact HXB'].
    - intros neg p HNUM HNEG HS HP.
      pose proof (B_range bs p (ok_bytes _ OK)) as HBP.
      apply (TAIL neg HNUM HNEG HS); [lia | lia | lia | apply Z.mod_small; lia].
  Qed.
End NumA.
