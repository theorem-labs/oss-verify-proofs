(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S7AdlerBase S7Adler_code FuzzAdlerLib S7AdlerA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler_fold adler_blocks csub lo16 hi16 byte_at.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition KP : list reg := [1; 2; 3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition LK : list reg := [1; 2; 3; 4; 5; 6; 7; 10; 11; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%bv.
Definition AMAGICv : Z := 4223091239536077.
Definition NEG5552 : Z := 18446744073709546064.

Section ADLB.
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.
  Hypothesis Hl0 : 0 <= len0.

  #[local] Abbreviation BA := (byte_at RSEGS m).
  #[local] Abbreviation BS := (bytes_at RSEGS m).
  #[local] Abbreviation PL := (bytes_at RSEGS m adr0 (Z.to_nat len0)).

  Ltac solve_ka := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption|]; first [assumption | solve_lkeeps | eapply lkeeps_trans; eassumption] ].
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_ka ].
  Ltac step_auipc F D := stepi F D; znorm;
    try match goal with |- context [regupd _ _ (v_auipc ?p ?i)] => wlit_closed (v_auipc p i) end.
  Ltac ld_amag F D :=
    chain_step;
    [ reflexivity
    | eapply step_ld with (v := Z_to_bv 64 4223091239536077);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with AMAG by (unfold AMAG; lia) end;
        apply rd_amag; exact Himg
      | exact amag_bs_v ]
    | step_simpl; gres ].

  Ltac kept K H r := rewrite (K r) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact H.


  Lemma blk_loop : forall (c : nat) regs (i : nat) (ab : Z * Z) (rem : Z),
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 5 = Z_to_bv 64 5552 -> getr regs 6 = Z_to_bv 64 NEG5552 ->
    getr regs 17 = Z_to_bv 64 AMAGICv -> getr regs 7 = Z_to_bv 64 65521 -> getr regs 28 = Z_to_bv 64 346 ->
    getr regs 16 = Z_to_bv 64 (Z.of_nat i) -> getr regs 15 = Z_to_bv 64 (adr0 + 5552 * Z.of_nat i) ->
    getr regs 12 = Z_to_bv 64 rem ->
    getr regs 14 = Z_to_bv 64 (fst (adler_blocks i ab PL)) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_blocks i ab PL)) ->
    0 <= fst ab <= 65535 -> 0 <= snd ab <= 65535 ->
    rem = len0 - 5552 * Z.of_nat i -> 5552 * Z.of_nat (S c) <= rem < 5552 * Z.of_nat (S c) + 5552 ->
    exists r, msteps RSEGS (mkst regs (0x1736c : word) m rom) (mkst r (0x17490 : word) m rom)
      /\ getr r 14 = Z_to_bv 64 (fst (adler_blocks (i + S c) ab PL))
      /\ getr r 13 = Z_to_bv 64 (snd (adler_blocks (i + S c) ab PL))
      /\ getr r 15 = Z_to_bv 64 (adr0 + 5552 * Z.of_nat (i + S c))
      /\ getr r 12 = Z_to_bv 64 (rem - 5552 * Z.of_nat (S c))
      /\ getr r 16 = Z_to_bv 64 (Z.of_nat (i + S c))
      /\ lkeeps LK regs r.
  Proof.
    induction c as [|c IH]; intros regs i ab rem R11 R5 R6 R17 R7 R28 R16 R15 R12 R14 R13 Hab1 Hab2 Hrem Hc.
    -
      set (q := adr0 + 5552 * Z.of_nat i) in *.
      set (ab1 := adler_blocks i ab PL) in *.
      pose proof (adler_blocks_bound16 i (fst ab) (snd ab) PL Hab1 Hab2) as Hb16.
      rewrite <- surjective_pairing in Hb16. fold ab1 in Hb16. destruct Hb16 as [HbA HbB].
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x17380 : word) m rom)
               (fun r => getr r 30 = Z_to_bv 64 (q + Z.of_nat 0)
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab1 (BS q 0)))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab1 (BS q 0)))
                         /\ getr r 29 = Z_to_bv 64 (q + Z.of_nat 0 + 16 * Z.of_nat 347)
                         /\ getr r 12 = Z_to_bv 64 (rem - 5552)
                         /\ getr r 11 = Z_to_bv 64 adr0 /\ getr r 5 = Z_to_bv 64 5552 /\ getr r 6 = Z_to_bv 64 NEG5552
                         /\ getr r 17 = Z_to_bv 64 AMAGICv /\ getr r 7 = Z_to_bv 64 65521 /\ getr r 28 = Z_to_bv 64 346
                         /\ getr r 16 = Z_to_bv 64 (Z.of_nat i) /\ getr r 15 = Z_to_bv 64 q
                         /\ lkeeps LK regs r)).
      { eexists. split.
        - stepz F_17268 D_17268. stepz F_1726c D_1726c. stepz F_17270 D_17270.
          stepz F_17274 D_17274.
          match goal with |- context [Z_to_bv 64 (rem + NEG5552)] =>
            replace (Z_to_bv 64 (rem + NEG5552)) with (Z_to_bv 64 (rem - 5552) : word)
              by (apply zv_eq; unfold NEG5552; rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia) end.
          stepz F_17278 D_17278.
          apply mst_refl.
        - rewrite adler_fold_bytes_0. post. }
      cbv beta. intros r1 (S30 & S14 & S13 & S29 & S12 & S11 & S5 & S6 & S17 & S7 & S28 & S16 & S15 & K1).
      destruct (b16_loop m rom adr0 len0 Hrd Hnw Ha0 346 r1 ab1 q 0 S30 S14 S13 S29 ltac:(lia) ltac:(lia))
        as (r2 & M2 & A2 & B2 & C2 & K2).
      change (0 + 16 * 347)%nat with (Z.to_nat NMAX) in A2, B2.
      pose proof (sums_range64' ab1 (BS q (Z.to_nat NMAX)) HbA HbB (bytes_at_bytes _ _ _ _)
                    ltac:(rewrite Zlen_bytes_at; unfold NMAX; lia)) as [HA HB].
      destruct (bmod_run m rom r2 _ _ q (rem - 5552) (Z.of_nat i) A2 B2
                  ltac:(kept K2 S17 (17%bv : reg)) ltac:(kept K2 S7 (7%bv : reg)) ltac:(kept K2 S15 (15%bv : reg)) ltac:(kept K2 S5 (5%bv : reg))
                  ltac:(kept K2 S12 (12%bv : reg)) ltac:(kept K2 S16 (16%bv : reg)) HA HB ltac:(lia))
        as (r3 & M3 & A3 & B3 & C3 & T3 & I3 & K3).
      assert (E28 : getr r3 28 = Z_to_bv 64 346) by (rewrite (K3 (28%bv : reg)), (K2 (28%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact S28).
      assert (E12 : getr r3 12 = Z_to_bv 64 (rem - 5552)) by (rewrite (K3 (12%bv : reg)), (K2 (12%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact S12).
      assert (Hsh : Z.shiftr (rem - 5552) 4 < 347).
      { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_lt_upper_bound; lia. }
      assert (Hsh0 : 0 <= Z.shiftr (rem - 5552) 4) by (apply Z.shiftr_nonneg; lia).
      eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
        stepb_ft F_17388 D_17388 ltac:(condZ).
        apply mst_refl.
      + gres. rewrite A3. replace (i + 1)%nat with (S i) by lia.
        rewrite (adler_blocks_bytes_S RSEGS m i ab adr0 (Z.to_nat len0)) by lia. reflexivity.
      + gres. rewrite B3. replace (i + 1)%nat with (S i) by lia.
        rewrite (adler_blocks_bytes_S RSEGS m i ab adr0 (Z.to_nat len0)) by lia. reflexivity.
      + gres. rewrite C3. zbv.
      + gres. rewrite E12. zbv.
      + gres. rewrite I3. zbv.
      + eapply lkeeps_trans; [exact K1|].
        intros x Hx. rewrite (K3 x), (K2 x); [reflexivity| |]; revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto]).
    -
      set (q := adr0 + 5552 * Z.of_nat i) in *.
      set (ab1 := adler_blocks i ab PL) in *.
      pose proof (adler_blocks_bound16 i (fst ab) (snd ab) PL Hab1 Hab2) as Hb16.
      rewrite <- surjective_pairing in Hb16. fold ab1 in Hb16. destruct Hb16 as [HbA HbB].
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x17380 : word) m rom)
               (fun r => getr r 30 = Z_to_bv 64 (q + Z.of_nat 0)
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab1 (BS q 0)))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab1 (BS q 0)))
                         /\ getr r 29 = Z_to_bv 64 (q + Z.of_nat 0 + 16 * Z.of_nat 347)
                         /\ getr r 12 = Z_to_bv 64 (rem - 5552)
                         /\ getr r 11 = Z_to_bv 64 adr0 /\ getr r 5 = Z_to_bv 64 5552 /\ getr r 6 = Z_to_bv 64 NEG5552
                         /\ getr r 17 = Z_to_bv 64 AMAGICv /\ getr r 7 = Z_to_bv 64 65521 /\ getr r 28 = Z_to_bv 64 346
                         /\ getr r 16 = Z_to_bv 64 (Z.of_nat i) /\ getr r 15 = Z_to_bv 64 q
                         /\ lkeeps LK regs r)).
      { eexists. split.
        - stepz F_17268 D_17268. stepz F_1726c D_1726c. stepz F_17270 D_17270.
          stepz F_17274 D_17274.
          match goal with |- context [Z_to_bv 64 (rem + NEG5552)] =>
            replace (Z_to_bv 64 (rem + NEG5552)) with (Z_to_bv 64 (rem - 5552) : word)
              by (apply zv_eq; unfold NEG5552; rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia) end.
          stepz F_17278 D_17278.
          apply mst_refl.
        - rewrite adler_fold_bytes_0. post. }
      cbv beta. intros r1 (S30 & S14 & S13 & S29 & S12 & S11 & S5 & S6 & S17 & S7 & S28 & S16 & S15 & K1).
      destruct (b16_loop m rom adr0 len0 Hrd Hnw Ha0 346 r1 ab1 q 0 S30 S14 S13 S29 ltac:(lia) ltac:(lia))
        as (r2 & M2 & A2 & B2 & C2 & K2).
      change (0 + 16 * 347)%nat with (Z.to_nat NMAX) in A2, B2.
      pose proof (sums_range64' ab1 (BS q (Z.to_nat NMAX)) HbA HbB (bytes_at_bytes _ _ _ _)
                    ltac:(rewrite Zlen_bytes_at; unfold NMAX; lia)) as [HA HB].
      destruct (bmod_run m rom r2 _ _ q (rem - 5552) (Z.of_nat i) A2 B2
                  ltac:(kept K2 S17 (17%bv : reg)) ltac:(kept K2 S7 (7%bv : reg)) ltac:(kept K2 S15 (15%bv : reg)) ltac:(kept K2 S5 (5%bv : reg))
                  ltac:(kept K2 S12 (12%bv : reg)) ltac:(kept K2 S16 (16%bv : reg)) HA HB ltac:(lia))
        as (r3 & M3 & A3 & B3 & C3 & T3 & I3 & K3).
      assert (K13 : lkeeps LK regs r3).
      { eapply lkeeps_trans; [exact K1|].
        intros x Hx. rewrite (K3 x), (K2 x); [reflexivity| |]; revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto]). }
      assert (E12 : getr r3 12 = Z_to_bv 64 (rem - 5552)) by (rewrite (K3 (12%bv : reg)), (K2 (12%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact S12).
      assert (E28 : getr r3 28 = Z_to_bv 64 346) by (rewrite (K3 (28%bv : reg)), (K2 (28%bv : reg)) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact S28).
      assert (Hsh : 347 <= Z.shiftr (rem - 5552) 4).
      { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_le_lower_bound; lia. }
      assert (Hsh2 : Z.shiftr (rem - 5552) 4 < two64).
      { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_lt_upper_bound; lia. }
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) in I3 by lia.
      replace (q + 5552) with (adr0 + 5552 * Z.of_nat (S i)) in C3 by lia.
      assert (A3' : getr r3 14 = Z_to_bv 64 (fst (adler_blocks (S i) ab PL))).
      { rewrite A3, (adler_blocks_bytes_S RSEGS m i ab adr0 (Z.to_nat len0)) by lia. reflexivity. }
      assert (B3' : getr r3 13 = Z_to_bv 64 (snd (adler_blocks (S i) ab PL))).
      { rewrite B3, (adler_blocks_bytes_S RSEGS m i ab adr0 (Z.to_nat len0)) by lia. reflexivity. }
      destruct (IH r3 (S i) ab (rem - 5552)
                  ltac:(kept K13 R11 (11%bv : reg)) ltac:(kept K13 R5 (5%bv : reg)) ltac:(kept K13 R6 (6%bv : reg))
                  ltac:(kept K13 R17 (17%bv : reg)) ltac:(kept K13 R7 (7%bv : reg)) ltac:(kept K13 R28 (28%bv : reg))
                  I3 C3 E12 A3' B3' Hab1 Hab2 ltac:(lia) ltac:(lia))
        as (r4 & M4 & A4 & B4 & C4 & T4 & I4 & K4).
      eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
      + eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
        stepb_tk F_17388 D_17388 ltac:(rwR; rewrite (kept K13 R28 (28%bv : reg)) || idtac; condZ).
        exact M4.
      + rewrite A4. replace (i + S (S c))%nat with (S i + S c)%nat by lia. reflexivity.
      + rewrite B4. replace (i + S (S c))%nat with (S i + S c)%nat by lia. reflexivity.
      + rewrite C4. zbv.
      + rewrite T4. zbv.
      + rewrite I4. zbv.
      + eapply lkeeps_trans; [exact K13 | exact K4].
  Qed.


  Lemma lkeeps_KP : forall l r1 r2, lkeeps l r1 r2 -> incl KP l -> lkeeps KP r1 r2.
  Proof. intros l r1 r2 H Hi x Hx. apply H, Hi, Hx. Qed.
  Ltac toKP H := apply (lkeeps_KP _ _ _ H); incl_dec.
  Ltac kp_chain := repeat match goal with
    | |- lkeeps KP ?a ?a => apply lkeeps_refl
    | |- lkeeps KP _ (regupd _ _ _) => solve_lkeeps
    | H : lkeeps _ ?a ?b |- lkeeps KP ?a ?c =>
        first [ constr_eq b c; toKP H
              | apply (lkeeps_trans KP a b c); [toKP H|] ] end.
  Ltac postK := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_ka | kp_chain ].


  Lemma tail8_run : forall regs (ab : Z * Z) (q : Z) (n : nat) (rest : Z),
    getr regs 10 = Z_to_bv 64 AMREF ->
    getr regs 15 = Z_to_bv 64 (q + Z.of_nat n) -> getr regs 12 = Z_to_bv 64 rest ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    0 < rest < 16 -> adr0 <= q -> q + Z.of_nat n + rest <= adr0 + len0 ->
    0 <= fst ab <= 65535 -> 0 <= snd ab <= 65535 -> Z.of_nat n + rest <= NMAX ->
    exists r, msteps RSEGS (mkst regs (0x17578 : word) m rom) (mkst r (0x175e0 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor ((snd (adler_fold ab (BS q (n + Z.to_nat rest))) mod BASE) * 2 ^ 16)
                                      (fst (adler_fold ab (BS q (n + Z.to_nat rest))) mod BASE))
      /\ lkeeps KP regs r.
  Proof.
    intros regs ab q n rest R10 R15 R12 R14 R13 Hrest Hq Hfit Hab1 Hab2 Hn.
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x1757c : word) m rom)
             (fun r => getr r 15 = Z_to_bv 64 (q + Z.of_nat n)
                       /\ getr r 12 = Z_to_bv 64 (q + Z.of_nat n + Z.of_nat (S (Z.to_nat (rest - 1))))
                       /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n)))
                       /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n)))
                       /\ getr r 10 = Z_to_bv 64 AMREF /\ lkeeps KP regs r)).
    { eexists. split.
      - stepz F_17474 D_17474. apply mst_refl.
      - post. }
    cbv beta. intros r1 (S15 & S12 & S14 & S13 & S10 & K1).
    destruct (tb_loop m rom adr0 len0 Hrd Hnw Ha0 (Z.to_nat (rest - 1)) r1 ab q n S15 S12 S14 S13 Hq ltac:(lia))
      as (r2 & M2 & A2 & B2 & K2).
    pose proof (sums_range64' ab (BS q (n + S (Z.to_nat (rest - 1)))) Hab1 Hab2 (bytes_at_bytes _ _ _ _)
                  ltac:(rewrite Zlen_bytes_at; lia)) as [HA HB].
    destruct (tmod_run m rom Himg r2 _ _ ltac:(kept K2 S10 (10%bv : reg)) A2 B2 HA HB) as (r3 & M3 & A3 & B3 & K3).
    destruct (comb_run m rom r3 _ _ A3 B3) as (r4 & M4 & V4 & K4).
    exists r4. split; [|split].
    - eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3 | exact M4].
    - rewrite V4. replace (n + Z.to_nat rest)%nat with (n + S (Z.to_nat (rest - 1)))%nat by lia. reflexivity.
    - kp_chain.
  Qed.

  Lemma tail_run : forall regs (ab : Z * Z) (q : Z) (n : nat) (rest : Z),
    getr regs 10 = Z_to_bv 64 AMREF ->
    getr regs 15 = Z_to_bv 64 (q + Z.of_nat n) -> getr regs 12 = Z_to_bv 64 rest ->
    getr regs 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n))) ->
    getr regs 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) ->
    0 <= rest < 16 -> adr0 <= q -> q + Z.of_nat n + rest <= adr0 + len0 ->
    0 <= fst ab <= 65535 -> 0 <= snd ab <= 65535 -> Z.of_nat n + rest <= NMAX ->
    exists r, msteps RSEGS (mkst regs (0x17574 : word) m rom) (mkst r (0x175e0 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (Z.lor ((snd (adler_fold ab (BS q (n + Z.to_nat rest))) mod BASE) * 2 ^ 16)
                                      (fst (adler_fold ab (BS q (n + Z.to_nat rest))) mod BASE))
      /\ lkeeps KP regs r.
  Proof.
    intros regs ab q n rest R10 R15 R12 R14 R13 Hrest Hq Hfit Hab1 Hab2 Hn.
    destruct (Z.eq_dec rest 0) as [-> | Hne].
    - pose proof (sums_range64' ab (BS q n) Hab1 Hab2 (bytes_at_bytes _ _ _ _)
                    ltac:(rewrite Zlen_bytes_at; lia)) as [HA HB].
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x17594 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 AMREF
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n)))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) /\ lkeeps KP regs r)).
      { eexists. split.
        - stepb_tk F_17470 D_17470 ltac:(condZ). apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S14 & S13 & K1).
      destruct (tmod_run m rom Himg r1 _ _ S10 S14 S13 HA HB) as (r3 & M3 & A3 & B3 & K3).
      destruct (comb_run m rom r3 _ _ A3 B3) as (r4 & M4 & V4 & K4).
      exists r4. split; [|split].
      + eapply msteps_trans; [exact M3 | exact M4].
      + rewrite V4. replace (n + Z.to_nat 0)%nat with n by lia. reflexivity.
      + kp_chain.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x17578 : word) m rom)
               (fun r => getr r 10 = Z_to_bv 64 AMREF /\ getr r 15 = Z_to_bv 64 (q + Z.of_nat n)
                         /\ getr r 12 = Z_to_bv 64 rest
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS q n)))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS q n))) /\ lkeeps KP regs r)).
      { eexists. split.
        - stepb_ft F_17470 D_17470 ltac:(condZ). apply mst_refl.
        - post. }
      cbv beta. intros r1 (S10 & S15 & S12 & S14 & S13 & K1).
      destruct (tail8_run r1 ab q n rest S10 S15 S12 S14 S13 ltac:(lia) Hq Hfit Hab1 Hab2 Hn) as (r2 & M2 & V2 & K2).
      exists r2. split; [exact M2 | split; [exact V2 | kp_chain]].
  Qed.


  Lemma short_run : forall regs (a : Z),
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    getr regs 14 = Z_to_bv 64 (lo16 a) -> getr regs 13 = Z_to_bv 64 (hi16 a) ->
    len0 < 16 -> len0 <> 1 ->
    exists r, msteps RSEGS (mkst regs (0x172a8 : word) m rom) (mkst r (0x17320 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a PL)
      /\ lkeeps KP regs r.
  Proof.
    intros regs a R11 R12 R14 R13 H16 H1.
    pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    rewrite <- (adler_short_exit a PL) by (rewrite Zlen_bytes_at; lia). cbv zeta.
    pose proof (short_a_range (lo16 a) (hi16 a) PL Hlo (bytes_at_bytes _ _ _ _) ltac:(rewrite Zlen_bytes_at; lia)) as HA.
    pose proof (sums_range64 (lo16 a) (hi16 a) PL Hlo Hhi (bytes_at_bytes _ _ _ _)
                  ltac:(rewrite Zlen_bytes_at; unfold NMAX; lia)) as [_ HB].
    set (ab := (lo16 a, hi16 a)) in *.
    destruct (Z.eq_dec len0 0) as [Hz | Hnz].
    -
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x172d0 : word) m rom)
               (fun r => getr r 14 = Z_to_bv 64 (fst (adler_fold ab PL))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab PL)) /\ lkeeps KP regs r)).
      { eexists. split.
        - stepz F_171a4 D_171a4.
          stepb_ft F_171a8 D_171a8 ltac:(condZ).
          stepb_tk F_171ac D_171ac ltac:(condZ).
          apply mst_refl.
        - rewrite Hz. change (Z.to_nat 0) with 0%nat. rewrite adler_fold_bytes_0. subst ab. post. }
      cbv beta. intros r1 (S14 & S13 & K1).
      destruct (smod_run m rom Himg r1 _ _ S14 S13 ltac:(lia) HB) as (r2 & M2 & V2 & K2).
      exists r2. split; [exact M2 | split; [exact V2 | kp_chain]].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x172b8 : word) m rom)
               (fun r => getr r 11 = Z_to_bv 64 (adr0 + Z.of_nat 0)
                         /\ getr r 12 = Z_to_bv 64 (adr0 + Z.of_nat 0 + Z.of_nat (S (Z.to_nat (len0 - 1))))
                         /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS adr0 0)))
                         /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS adr0 0))) /\ lkeeps KP regs r)).
      { eexists. split.
        - stepz F_171a4 D_171a4.
          stepb_ft F_171a8 D_171a8 ltac:(condZ).
          stepb_ft F_171ac D_171ac ltac:(condZ).
          stepz F_171b0 D_171b0.
          apply mst_refl.
        - rewrite adler_fold_bytes_0. subst ab. post. }
      cbv beta. intros r1 (S11 & S12 & S14 & S13 & K1).
      destruct (sb_loop m rom adr0 len0 Hrd Hnw Ha0 (Z.to_nat (len0 - 1)) r1 ab adr0 0 S11 S12 S14 S13 ltac:(lia) ltac:(lia))
        as (r2 & M2 & A2 & B2 & K2).
      replace (0 + S (Z.to_nat (len0 - 1)))%nat with (Z.to_nat len0) in A2, B2 by lia.
      destruct (smod_run m rom Himg r2 _ _ A2 B2 ltac:(lia) HB) as (r3 & M3 & V3 & K3).
      exists r3. split; [|split].
      + eapply msteps_trans; [exact M2 | exact M3].
      + exact V3.
      + kp_chain.
  Qed.

  Lemma mid_run : forall regs (a : Z),
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    getr regs 14 = Z_to_bv 64 (lo16 a) -> getr regs 13 = Z_to_bv 64 (hi16 a) ->
    16 <= len0 < NMAX ->
    exists r, msteps RSEGS (mkst regs (0x172a8 : word) m rom) (mkst r (0x175e0 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a PL)
      /\ lkeeps KP regs r.
  Proof.
    intros regs a R11 R12 R14 R13 Hlen. unfold NMAX in Hlen.
    pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    assert (Hnil : PL <> []).
    { intros E. apply (f_equal (@length Z)) in E. rewrite bytes_at_length in E. cbn in E. lia. }
    rewrite <- (adler_long_exit_cons a PL PL); cycle 1.
    { rewrite Zlen_bytes_at. lia. }
    { rewrite Zlen_bytes_at. replace (Z.of_nat (Z.to_nat len0) / NMAX) with 0 by (unfold NMAX; symmetry; apply Z.div_small; lia).
      reflexivity. }
    { exact Hnil. }
    cbv zeta. rewrite Zlen_bytes_at.
    replace (Z.of_nat (Z.to_nat len0) / NMAX) with 0 by (unfold NMAX; symmetry; apply Z.div_small; lia).
    change (Z.to_nat 0) with 0%nat. rewrite adler_blocks_0.
    set (ab := (lo16 a, hi16 a)).
    pose proof (Z.div_mod len0 16 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound len0 16 ltac:(lia)) as Hmb.
    assert (Hq : 1 <= len0 / 16) by (apply Z.div_le_lower_bound; lia).
    set (k := Z.to_nat (len0 / 16 - 1)).
    assert (Hk : Z.of_nat (S k) = len0 / 16) by (subst k; lia).
    assert (Hsh : Z.shiftr len0 4 < 347).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_lt_upper_bound; lia. }
    assert (Hsh0 : 0 <= Z.shiftr len0 4) by (apply Z.shiftr_nonneg; lia).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x174a8 : word) m rom)
             (fun r => getr r 15 = Z_to_bv 64 (adr0 + Z.of_nat 0)
                       /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab (BS adr0 0)))
                       /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab (BS adr0 0)))
                       /\ getr r 12 = Z_to_bv 64 (16 * Z.of_nat (S k) + len0 mod 16)
                       /\ getr r 11 = Z_to_bv 64 15
                       /\ getr r 10 = Z_to_bv 64 AMREF /\ lkeeps KP regs r)).
    { eexists. split.
      - stepz F_171a4 D_171a4.
        stepb_tk F_171a8 D_171a8 ltac:(condZ).
        stepi F_17230 D_17230; znorm. rewrite (zv_srli len0 4) by lia.
        stepz F_17234 D_17234.
        step_auipc F_17238 D_17238.
        stepb_tk F_1723c D_1723c ltac:(condZ).
        stepz F_1739c D_1739c.
        stepz F_173a0 D_173a0.
        apply mst_refl.
      - rewrite adler_fold_bytes_0. subst ab. unfold AMREF. post. }
    cbv beta. intros r1 (S15 & S14 & S13 & S12 & S11 & S10 & K1).
    destruct (d16_loop m rom adr0 len0 Hrd Hnw Ha0 k r1 ab adr0 0 (len0 mod 16) S15 S14 S13 S12 S11
                ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & M2 & A2 & B2 & C2 & N2 & E2 & K2).
    destruct (tail_run r2 ab adr0 (0 + 16 * S k) (len0 mod 16) ltac:(kept K2 S10 (10%bv : reg))
                ltac:(rewrite C2; zbv) N2 A2 B2 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(subst ab; cbn [fst]; lia) ltac:(subst ab; cbn [snd]; lia) ltac:(unfold NMAX; lia))
      as (r3 & M3 & V3 & K3).
    exists r3. split; [|split].
    - eapply msteps_trans; [exact M2 | exact M3].
    - rewrite V3. replace (0 + 16 * S k + Z.to_nat (len0 mod 16))%nat with (Z.to_nat len0) by lia. reflexivity.
    - kp_chain.
  Qed.

  Lemma long_run : forall regs (a : Z),
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    getr regs 14 = Z_to_bv 64 (lo16 a) -> getr regs 13 = Z_to_bv 64 (hi16 a) ->
    NMAX <= len0 ->
    exists r, msteps RSEGS (mkst regs (0x172a8 : word) m rom) (mkst r (0x175e0 : word) m rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a PL)
      /\ lkeeps KP regs r.
  Proof.
    intros regs a R11 R12 R14 R13 Hlen. unfold NMAX in Hlen.
    pose proof (lo16_le a) as Hlo. pose proof (hi16_le a) as Hhi.
    set (ab := (lo16 a, hi16 a)).
    pose proof (Z.div_mod len0 5552 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound len0 5552 ltac:(lia)) as Hmb.
    assert (Hq : 1 <= len0 / 5552) by (apply Z.div_le_lower_bound; lia).
    set (nb := len0 / 5552) in *.
    set (c := Z.to_nat (nb - 1)).
    assert (Hc : Z.of_nat (S c) = nb) by (subst c; lia).
    assert (Hsh : 347 <= Z.shiftr len0 4).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_le_lower_bound; lia. }
    assert (Hsh2 : Z.shiftr len0 4 < two64).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply Z.div_lt_upper_bound; lia. }
    assert (Hnbl : Zlen PL / NMAX = nb) by (rewrite Zlen_bytes_at; unfold NMAX; subst nb; f_equal; lia).
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x1736c : word) m rom)
             (fun r => getr r 11 = Z_to_bv 64 adr0 /\ getr r 5 = Z_to_bv 64 5552 /\ getr r 6 = Z_to_bv 64 NEG5552
                       /\ getr r 17 = Z_to_bv 64 AMAGICv /\ getr r 7 = Z_to_bv 64 65521 /\ getr r 28 = Z_to_bv 64 346
                       /\ getr r 16 = Z_to_bv 64 (Z.of_nat 0) /\ getr r 15 = Z_to_bv 64 (adr0 + 5552 * Z.of_nat 0)
                       /\ getr r 12 = Z_to_bv 64 len0
                       /\ getr r 14 = Z_to_bv 64 (fst (adler_blocks 0 ab PL))
                       /\ getr r 13 = Z_to_bv 64 (snd (adler_blocks 0 ab PL))
                       /\ getr r 10 = Z_to_bv 64 AMREF /\ lkeeps KP regs r)).
    { eexists. split.
      - stepz F_171a4 D_171a4.
        stepb_tk F_171a8 D_171a8 ltac:(condZ).
        stepi F_17230 D_17230; znorm. rewrite (zv_srli len0 4) by lia.
        stepz F_17234 D_17234.
        step_auipc F_17238 D_17238.
        stepb_ft F_1723c D_1723c ltac:(condZ).
        stepz F_17240 D_17240. stepz F_17244 D_17244. stepz F_17248 D_17248.
        ld_amag F_1724c D_1724c.
        stepz F_17250 D_17250. stepz F_17254 D_17254. stepz F_17258 D_17258. stepz F_1725c D_1725c.
        stepz F_17260 D_17260. stepz F_17264 D_17264.
        apply mst_refl.
      - rewrite adler_blocks_0. subst ab. unfold AMREF, AMAGICv, NEG5552. post. }
    cbv beta. intros r1 (S11 & S5 & S6 & S17 & S7 & S28 & S16 & S15 & S12 & S14 & S13 & S10 & K1).
    destruct (blk_loop c r1 0 ab len0 S11 S5 S6 S17 S7 S28 S16 S15 S12 S14 S13
                ltac:(subst ab; cbn [fst]; lia) ltac:(subst ab; cbn [snd]; lia) ltac:(lia) ltac:(lia))
      as (r2 & M2 & A2 & B2 & C2 & N2 & I2 & K2).
    cbn [Nat.add] in A2, B2, C2, I2.
    assert (E10 : getr r2 10 = Z_to_bv 64 AMREF) by (kept K2 S10 (10%bv : reg)).
    set (ab1 := adler_blocks (S c) ab PL) in *.
    pose proof (adler_blocks_bound16 (S c) (lo16 a) (hi16 a) PL Hlo Hhi) as Hb16. fold ab ab1 in Hb16.
    destruct Hb16 as [Hb1 Hb2].
    set (p := adr0 + 5552 * Z.of_nat (S c)) in *.
    set (rem := len0 - 5552 * Z.of_nat (S c)) in *.
    assert (Hrem : 0 <= rem < 5552) by (subst rem; lia).
    assert (Hrest : skipn (Z.to_nat (NMAX * nb)) PL = BS p (Z.to_nat rem)).
    { rewrite <- Hc. rewrite (adler_rest_bytes RSEGS m adr0 (Z.to_nat len0) (S c)) by lia.
      subst p rem. f_equal. unfold NMAX. lia. }
    destruct (Z.eq_dec rem 0) as [Hz | Hnz].
    -
      rewrite <- (adler_long_exit_nil a PL); cycle 1.
      { rewrite Zlen_bytes_at. lia. }
      { rewrite Hnbl, Hrest, Hz. reflexivity. }
      cbv zeta. rewrite Hnbl, <- Hc, Nat2Z.id. fold ab. fold ab1.
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x175d8 : word) m rom)
               (fun r => getr r 14 = Z_to_bv 64 (fst ab1) /\ getr r 13 = Z_to_bv 64 (snd ab1) /\ lkeeps KP r1 r)).
      { eexists. split.
        - eapply msteps_trans; [exact M2|].
          stepb_tk F_1738c D_1738c ltac:(condZ). apply mst_refl.
        - postK. }
      cbv beta. intros r3 (T14 & T13 & K3).
      destruct (comb_run m rom r3 _ _ T14 T13) as (r4 & M4 & V4 & K4).
      exists r4. split; [exact M4 | split; [exact V4 | kp_chain]].
    - rewrite <- (adler_long_exit_cons a PL (BS p (Z.to_nat rem))); cycle 1.
      { rewrite Zlen_bytes_at. lia. }
      { rewrite Hnbl. exact Hrest. }
      { intros E. apply (f_equal (@length Z)) in E. rewrite bytes_at_length in E. cbn in E. lia. }
      cbv zeta. rewrite Hnbl, <- Hc, Nat2Z.id. fold ab. fold ab1.
      destruct (Z.lt_ge_cases rem 16) as [Hsmall | Hbig].
      +
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x17578 : word) m rom)
                 (fun r => getr r 10 = Z_to_bv 64 AMREF /\ getr r 15 = Z_to_bv 64 (p + Z.of_nat 0)
                           /\ getr r 12 = Z_to_bv 64 rem
                           /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab1 (BS p 0)))
                           /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab1 (BS p 0))) /\ lkeeps KP r1 r)).
        { eexists. split.
          - eapply msteps_trans; [exact M2|].
            stepb_ft F_1738c D_1738c ltac:(condZ).
            stepz F_17390 D_17390.
            stepb_ft F_17394 D_17394 ltac:(condZ).
            stepz F_17398 D_17398.
            apply mst_refl.
          - rewrite adler_fold_bytes_0. postK. }
        cbv beta. intros r3 (T10 & T15 & T12 & T14 & T13 & K3).
        destruct (tail8_run r3 ab1 p 0 rem T10 T15 T12 T14 T13 ltac:(lia) ltac:(lia) ltac:(lia) Hb1 Hb2 ltac:(unfold NMAX; lia))
          as (r4 & M4 & V4 & K4).
        exists r4. split; [exact M4 | split; [rewrite V4; reflexivity | kp_chain]].
      +
        pose proof (Z.div_mod rem 16 ltac:(lia)) as Hdm2. pose proof (Z.mod_pos_bound rem 16 ltac:(lia)) as Hmb2.
        assert (Hq2 : 1 <= rem / 16) by (apply Z.div_le_lower_bound; lia).
        set (k := Z.to_nat (rem / 16 - 1)).
        assert (Hk : Z.of_nat (S k) = rem / 16) by (subst k; lia).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x174a8 : word) m rom)
                 (fun r => getr r 15 = Z_to_bv 64 (p + Z.of_nat 0)
                           /\ getr r 14 = Z_to_bv 64 (fst (adler_fold ab1 (BS p 0)))
                           /\ getr r 13 = Z_to_bv 64 (snd (adler_fold ab1 (BS p 0)))
                           /\ getr r 12 = Z_to_bv 64 (16 * Z.of_nat (S k) + rem mod 16)
                           /\ getr r 11 = Z_to_bv 64 15
                           /\ getr r 10 = Z_to_bv 64 AMREF /\ lkeeps KP r1 r)).
        { eexists. split.
          - eapply msteps_trans; [exact M2|].
            stepb_ft F_1738c D_1738c ltac:(condZ).
            stepz F_17390 D_17390.
            stepb_tk F_17394 D_17394 ltac:(condZ).
            stepz F_173a0 D_173a0.
            apply mst_refl.
          - rewrite adler_fold_bytes_0. postK. }
        cbv beta. intros r3 (T15 & T14 & T13 & T12 & T11 & T10 & K3).
        destruct (d16_loop m rom adr0 len0 Hrd Hnw Ha0 k r3 ab1 p 0 (rem mod 16) T15 T14 T13 T12 T11
                    ltac:(lia) ltac:(lia) ltac:(lia)) as (r4 & M4 & A4 & B4 & C4 & N4 & E4 & K4).
        destruct (tail_run r4 ab1 p (0 + 16 * S k) (rem mod 16) ltac:(kept K4 T10 (10%bv : reg))
                    ltac:(rewrite C4; zbv) N4 A4 B4 ltac:(lia) ltac:(lia) ltac:(lia) Hb1 Hb2 ltac:(unfold NMAX; lia))
          as (r5 & M5 & V5 & K5).
        exists r5. split; [|split].
        * eapply msteps_trans; [exact M4 | exact M5].
        * rewrite V5. replace (0 + 16 * S k + Z.to_nat (rem mod 16))%nat with (Z.to_nat rem) by lia. reflexivity.
        * kp_chain.
  Qed.

  Theorem body_run : forall regs (a : Z),
    getr regs 11 = Z_to_bv 64 adr0 -> getr regs 12 = Z_to_bv 64 len0 ->
    getr regs 14 = Z_to_bv 64 (lo16 a) -> getr regs 13 = Z_to_bv 64 (hi16 a) ->
    len0 <> 1 ->
    exists r (pc' : word), msteps RSEGS (mkst regs (0x172a8 : word) m rom) (mkst r pc' m rom)
      /\ (pc' = (0x17320%bv : word) \/ pc' = (0x175e0%bv : word))
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a PL)
      /\ lkeeps KP regs r.
  Proof.
    intros regs a R11 R12 R14 R13 H1.
    destruct (Z.lt_ge_cases len0 16) as [Hs | Hl].
    - destruct (short_run regs a R11 R12 R14 R13 Hs H1) as (r & M & V & K).
      eexists r, _. split; [exact M|]. split; [left; reflexivity|]. split; assumption.
    - destruct (Z.lt_ge_cases len0 NMAX) as [Hm | Hb].
      + destruct (mid_run regs a R11 R12 R14 R13 ltac:(lia)) as (r & M & V & K).
        eexists r, _. split; [exact M|]. split; [right; reflexivity|]. split; assumption.
      + destruct (long_run regs a R11 R12 R14 R13 Hb) as (r & M & V & K).
        eexists r, _. split; [exact M|]. split; [right; reflexivity|]. split; assumption.
  Qed.
End ADLB.
End FXG.
