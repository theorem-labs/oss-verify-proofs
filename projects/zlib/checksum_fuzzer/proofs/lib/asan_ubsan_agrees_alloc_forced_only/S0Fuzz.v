(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import S0Fuzz_crc S0Fuzz_adler.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S0FuzzBase S0Fuzz_code S0FuzzIface S0FuzzStmt
  S0Fuzz_cop S0Fuzz_gen S0Fuzz_comb S0Fuzz_adlc S0FuzzH1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkHarness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : FPState}.

Lemma entry_out_cond : forall n, 0 <= n < 2 ^ 64 -> ~ (1 <= n <= 1048576) ->
  c_ltu (Z_to_bv 64 (n + 18446744073708503039)) (Z_to_bv 64 18446744073708503040) = true.
Proof.
  intros n Hn Hout. pose proof (entry_test_out n Hn Hout) as E. unfold LIM1, LIM2 in E.
  rewrite zv_add in E. exact E.
Qed.

Lemma D_nil : forall mem data, D mem data 0 = [].
Proof. intros. reflexivity. Qed.

End FXG.
Ltac xfer K H H2 :=
  lazymatch type of K with keeps_cs ?ra ?rb =>
    lazymatch type of H with getr _ ?i = ?v =>
      assert (H2 : getr rb i = v) by (rewrite (K i) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact H)
    end
  end.
Ltac retok := apply ret_ok_even; reflexivity.
Ltac post :=
  try unfold hk; repeat split; gres; rwR;
  first [ reflexivity | assumption | lia | f_equal; lia | bveq | solve_lkeeps ].
Section FXG. Context {fx : FPState}.

Lemma chunk_arith : forall n b q, 1 <= b -> 0 <= n -> q = n / b ->
  (0 + q * b <= n < 0 + (q + 1) * b) /\ n mod b = n - q * b /\ 0 <= q * b.
Proof.
  intros n b q Hb Hn Hq.
  pose proof (Z.div_mod n b ltac:(lia)) as E. pose proof (Z.mod_pos_bound n b ltac:(lia)) as R.
  assert (Hq0 : 0 <= q) by (rewrite Hq; apply Z.div_pos; lia).
  rewrite <- Hq in E. nia.
Qed.

Section MAIN.
  Variables (mem : word -> option byte) (sp ret : word) (rom : word -> option byte).
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : FR <= bv_unsigned sp.
  Hypothesis Hstk : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - FR)) (Z.to_nat FR) = true.

  #[local] Abbreviation usp := (bv_unsigned sp).
  #[local] Abbreviation W8 v := (word_to_le_bytes 8 v).
  #[local] Abbreviation M13r := (M13 mem sp).

  Lemma keeps_cs_of : forall regs r,
    lkeeps hk regs r -> getr r 1 = getr regs 1 -> getr r 2 = getr regs 2 -> getr r 8 = getr regs 8 ->
    getr r 9 = getr regs 9 -> getr r 18 = getr regs 18 -> getr r 19 = getr regs 19 ->
    getr r 20 = getr regs 20 -> getr r 21 = getr regs 21 -> getr r 22 = getr regs 22 ->
    getr r 23 = getr regs 23 -> getr r 24 = getr regs 24 -> getr r 25 = getr regs 25 ->
    getr r 26 = getr regs 26 -> getr r 27 = getr regs 27 -> keeps_cs regs r.
  Proof.
    intros regs r K E1 E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 x Hx. cbv [callee_saved In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [ first [ assumption | apply K; cbv [hk In]; (first [solve [liafast_keep_section; tauto] | tauto]) ] |]).
    destruct Hx.
  Qed.

  Lemma M13_slots : forall regs,
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 8)) 8 = Some (W8 (getr regs 1)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 16)) 8 = Some (W8 (getr regs 8)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 24)) 8 = Some (W8 (getr regs 9)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 32)) 8 = Some (W8 (getr regs 18)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 40)) 8 = Some (W8 (getr regs 19)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 48)) 8 = Some (W8 (getr regs 20)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 56)) 8 = Some (W8 (getr regs 21)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 64)) 8 = Some (W8 (getr regs 22)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 72)) 8 = Some (W8 (getr regs 23)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 80)) 8 = Some (W8 (getr regs 24)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 88)) 8 = Some (W8 (getr regs 25)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 96)) 8 = Some (W8 (getr regs 26)) /\
    rdn RSEGS (M13r regs) (Z_to_bv 64 (usp - 104)) 8 = Some (W8 (getr regs 27)).
  Proof.
    intros regs. pose proof (u64_range sp). unfold FR in Hsp. unfold M13.
    repeat split; rdn_solve.
  Qed.

  Lemma M13_img : forall regs (data : word) (n : Z), fzH mem sp data n -> img_ok (M13r regs).
  Proof.
    intros regs data n HF i Hri. pose proof (u64_range sp).
    destruct (M13_frame mem sp Hsp regs) as [Ho _]. rewrite Ho; [apply (Fimg _ _ _ _ HF); exact Hri|].
    cbn [outside FRR]. split; [|exact I]. pose proof (frame_off_ro mem sp data n HF).
    unfold in_rng, FR, RO_LO, RO_HI in *. rewrite !u64_lit by lia. lia.
  Qed.

  Lemma fuzz_trivial : forall regs (n : Z),
    getr regs 1 = ret -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 n ->
    0 <= n < 2 ^ 64 -> ~ (1 <= n <= 1048576) ->
    exists regs' mem',
      msteps RSEGS (mkst regs (0x141f0 : word) mem rom) (mkst regs' ret mem' rom)
      /\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 0 /\ frame_mod mem mem' (FRR sp).
  Proof.
    intros regs n R1 R2 R11 Hn Hout. pose proof (u64_range sp).
    assert (R2' : getr regs 2 = Z_to_bv 64 usp) by (rewrite R2; apply word_zv).
    destruct (prologue_run mem sp rom Hsp Hstk regs (getr regs 10) n R2' eq_refl R11)
      as (r1 & M1 & P1 & P2 & P8 & P9 & P10 & P11 & P12 & K1).
    destruct (s0_crc32_null r1 (M13r regs) rom (0x14240%bv : word) P1 ltac:(retok) P11) as (r2 & M2 & V2 & K2).
    xfer K2 P2 Q2. xfer K2 P8 Q8.
    destruct (segB rom r2 (M13r regs) V2) as (r3 & M3 & A1 & A19 & A10 & A11 & A12 & A2 & A8 & A9 & K3).
    rewrite Q2 in A2. rewrite Q8 in A8.
    destruct (s0_adler32_null r3 (M13r regs) rom (0x14254%bv : word) A1 ltac:(retok) A11 A12) as (r4 & M4 & V4 & K4).
    xfer K4 A2 B2. xfer K4 A8 B8.
    assert (S5 : exists r, msteps RSEGS (mkst r4 (0x14254 : word) (M13r regs) rom) (mkst r (0x14480 : word) (M13r regs) rom)
      /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ lkeeps hk r4 r).
    { eexists. split.
      - unfold FR in Hsp.
        stepz F_141f4 D_141f4. stepz F_141f8 D_141f8. stepz F_141fc D_141fc.
        stepb_tk F_14200 D_14200 ltac:(rwR; apply entry_out_cond; first [exact Hout | lia]).
        apply mst_refl.
      - post. }
    destruct S5 as (r5 & M5 & C2 & K5).
    pose proof (M13_slots regs) as (E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
    destruct (epilogue_run sp ret rom Hret r5 (M13r regs) (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)
                (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                (getr regs 25) (getr regs 26) (getr regs 27) C2 R1
                E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27)
      as (r6 & M6 & Q10 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & K6).
    exists r6, (M13r regs). split; [|split; [|split]].
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
      eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. exact M6.
    - apply keeps_cs_of; try assumption.
      + intros x Hx. rewrite (K6 x Hx). rewrite (K5 x Hx). rewrite (K4 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])).
        rewrite (K3 x Hx). rewrite (K2 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx).
      + rewrite Z2, R2. symmetry. apply word_zv.
    - exact Q10.
    - apply M13_frame. exact Hsp.
  Qed.

  Section InRange.
    Variables (data : word) (n : Z).
    Hypothesis HF : fzH mem sp data n.
    Hypothesis Hapart : bv_unsigned data + n <= bv_unsigned sp - 192.

    #[local] Abbreviation udata := (bv_unsigned data).
    #[local] Abbreviation DD := (D mem data).
    #[local] Abbreviation CC := (CH mem data).

    Ltac ranges := pose proof (u64_range data); pose proof (u64_range sp); pose proof (Fn _ _ _ _ HF);
                   pose proof (Fnw _ _ _ _ HF); pose proof (Fdata _ _ _ _ HF); pose proof (B_range mem data);
                   unfold FR in Hsp.

    Section WithM0.
      Variable M0 : word -> option byte.
      Hypothesis HM0f : frame_mod mem M0 (FRR sp).
      #[local] Abbreviation MI := (MINV sp M0).

      Ltac minvs :=
        pose proof (minv_stk mem sp Hsp Hstk data n HF Hapart M0 HM0f) as Mstk;
        pose proof (minv_rd mem sp data n HF M0 HM0f) as Mrd;
        pose proof (minv_rd_off mem sp data n HF M0 HM0f) as Mrdo;
        pose proof (minv_bytes mem sp Hsp data n HF Hapart M0 HM0f) as Mbytes;
        pose proof (minv_frame mem sp Hsp data n HF Hapart M0) as Mframe;
        pose proof (minv_img sp M0) as Mimg.

      Section LOOPA.
        Variables (Bv Tv : Z).
        Hypothesis HBv : Bv = B mem data.

        Definition ADH (r : bvmap 5 word) (off A : Z) : Prop :=
          getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\
          getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\
          getr r 21 = Z_to_bv 64 Tv /\ getr r 26 = Z_to_bv 64 4294967295 /\
          getr r 22 = Z_to_bv 64 off /\ getr r 10 = Z_to_bv 64 A.
        Definition ADP (r : bvmap 5 word) (off A : Z) : Prop :=
          ADH r off A /\ getr r 11 = Z_to_bv 64 (off + Bv).

        Lemma adl_iter : forall regs m off A,
          ADH regs off A -> MI m -> 0 <= off -> off + Bv <= n -> A = adler_spec 1 (DD off) ->
          exists r m', msteps RSEGS (mkst regs (0x143f8 : word) m rom) (mkst r (0x14418 : word) m' rom)
            /\ ADP r (off + Bv) (adler_spec 1 (DD (off + Bv))) /\ MI m' /\ lkeeps hk regs r.
        Proof.
          intros regs m off A (R2 & R8 & R9 & R18 & R19 & R20 & R21 & R26 & R22 & R10) HM Hoff Hin HA.
          ranges. minvs. pose proof (Bv_range mem data Bv HBv) as HB'.
          assert (HAr : 0 <= A < two32) by (rewrite HA; apply adler_spec_1_range).
          assert (S1 : exists r, msteps RSEGS (mkst regs (0x143f8 : word) m rom) (mkst r (0x14e14 : word) m rom)
            /\ getr r 1 = (0x14410%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
            /\ getr r 10 = Z_to_bv 64 A /\ getr r 11 = Z_to_bv 64 (udata + off) /\ getr r 12 = Z_to_bv 64 Bv
            /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
            /\ getr r 19 = Z_to_bv 64 n /\ getr r 20 = Z_to_bv 64 Bv /\ getr r 21 = Z_to_bv 64 Tv
            /\ getr r 22 = Z_to_bv 64 off /\ getr r 26 = Z_to_bv 64 4294967295
            /\ lkeeps hk regs r).
          { eexists. split.
            - stepz F_14398 D_14398. rewrite <- (mod32_land A), (mod_small_32 A) by lia.
              stepz F_1439c D_1439c. stepz F_143a0 D_143a0. rewrite (mod_small_32 off) by lia.
              stepz F_143a4 D_143a4. stepz F_143a8 D_143a8. stepz F_143ac D_143ac.
              apply mst_refl.
            - post. }
          destruct S1 as (r1 & M1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A26 & K1).
          destruct (s0_adler32_z r1 m rom (0x14410%bv : word) (usp - 112) A (udata + off) Bv
                      A1 ltac:(retok) A2 A10 A11 A12
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(apply (Mstk m); [exact HM | lia | change (Z.of_nat 32) with 32; lia])
                      ltac:(intros _; lia) ltac:(apply Mimg; exact HM)
                      ltac:(apply (Mrdo m off Bv HM); lia))
            as (r2 & m2 & M2 & V2 & K2 & F2).
          rewrite (Mbytes m off Bv HM) in V2 by lia.
          change (bytes_at RSEGS mem (udata + off) (Z.to_nat Bv)) with (CC off Bv) in V2.
          assert (EA : adler32_z_model A (CC off Bv) = adler_spec 1 (DD (off + Bv))).
          { rewrite HA, D_CH by lia. apply harness_adler_stream; [apply D_bytes | apply CH_bytes]. }
          rewrite EA in V2. set (A' := adler_spec 1 (DD (off + Bv))) in V2.
          assert (HA'r : 0 <= A' < two32) by (subst A'; apply adler_spec_1_range).
          assert (HM2 : MI m2) by (eapply (Mframe m m2); [exact HM | exact F2 | lia | lia | lia]).
          xfer K2 A2 B2. xfer K2 A8 B8. xfer K2 A9 B9. xfer K2 A18 B18. xfer K2 A19 B19. xfer K2 A20 B20.
          xfer K2 A21 B21. xfer K2 A22 B22. xfer K2 A26 B26.
          assert (S3 : exists r, msteps RSEGS (mkst r2 (0x14410%bv : word) m2 rom) (mkst r (0x14418 : word) m2 rom)
            /\ ADP r (off + Bv) A' /\ lkeeps hk r2 r).
          { eexists. split.
            - stepz F_143b0 D_143b0.
              stepz F_143b4 D_143b4.
              zval (off + Bv + Bv) ltac:(rewrite mod_small_32 by lia; rewrite sx32_small by lia; f_equal; lia).
              apply mst_refl.
            - unfold ADP, ADH. post. }
          destruct S3 as (r3 & M3 & P3 & K3).
          exists r3, m2. split; [|split; [exact P3 | split; [exact HM2|]]].
          - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. exact M3.
          - intros x Hx. rewrite (K3 x Hx). rewrite (K2 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx).
        Qed.

        Lemma adl_loop : forall (k : nat) regs m off,
          ADP regs off (adler_spec 1 (DD off)) -> MI m -> 0 <= off ->
          off + Z.of_nat k * Bv <= n < off + (Z.of_nat k + 1) * Bv ->
          exists r m', msteps RSEGS (mkst regs (0x14418 : word) m rom) (mkst r (0x14424 : word) m' rom)
            /\ MI m' /\ lkeeps hk regs r
            /\ getr r 11 = Z_to_bv 64 (off + Z.of_nat k * Bv)
            /\ getr r 10 = Z_to_bv 64 (adler_spec 1 (DD (off + Z.of_nat k * Bv)))
            /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
            /\ getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 21 = Z_to_bv 64 Tv
            /\ getr r 26 = Z_to_bv 64 4294967295.
        Proof.
          induction k as [|k IH]; intros regs m off HP HM Hoff Hk.
          - change (Z.of_nat 0) with 0 in *. rewrite Z.mul_0_l, Z.add_0_r.
            destruct HP as ((R2 & R8 & R9 & R18 & R19 & R20 & R21 & R26 & R22 & R10) & R11).
            ranges. pose proof (Bv_range mem data Bv HBv) as HB'.
            assert (S : exists r, msteps RSEGS (mkst regs (0x14418 : word) m rom) (mkst r (0x14424 : word) m rom)
              /\ getr r 11 = Z_to_bv 64 off /\ getr r 10 = Z_to_bv 64 (adler_spec 1 (DD off))
              /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
              /\ getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 21 = Z_to_bv 64 Tv
              /\ getr r 26 = Z_to_bv 64 4294967295
              /\ lkeeps hk regs r).
            { eexists. split.
              - stepb_ft F_143b8 D_143b8 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_lt; lia).
                stepz F_143bc D_143bc. stepz F_143c0 D_143c0. rewrite (mod_small_32 off) by lia.
                apply mst_refl.
              - post. }
            destruct S as (r & M & V11 & V10 & V2 & V8 & V9 & V18 & V19 & V21 & V26 & K).
            exists r, m. split; [exact M|]. split; [exact HM|]. split; [exact K|]. repeat split; assumption.
          - pose proof (Bv_range mem data Bv HBv) as HB'.
            assert (Hk' : off + Bv + Z.of_nat k * Bv <= n < off + Bv + (Z.of_nat k + 1) * Bv)
              by (rewrite Nat2Z.inj_succ in Hk; lia).
            destruct HP as (HH & R11).
            pose proof HH as (R2 & R8 & R9 & R18 & R19 & R20 & R21 & R26 & R22 & R10). ranges.
            destruct (adl_iter regs m off _ HH HM Hoff ltac:(lia) eq_refl) as (r1 & m1 & M1 & HP1 & HM1 & K1).
            destruct (IH r1 m1 (off + Bv) HP1 HM1 ltac:(lia) Hk')
              as (r & m' & M & HM' & K & V11 & V10 & V2 & V8 & V9 & V18 & V19 & V21 & V26).
            exists r, m'. replace (off + Z.of_nat (S k) * Bv) with (off + Bv + Z.of_nat k * Bv) by lia.
            split.
            { stepb_tk F_143b8 D_143b8 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
              eapply msteps_trans; [exact M1 | exact M]. }
            split; [exact HM'|]. split; [eapply lkeeps_trans; [exact K1 | exact K]|].
            repeat split; assumption.
        Qed.

        Lemma phase3a : forall regs m (q : nat),
          getr regs 2 = Z_to_bv 64 (usp - 112) -> getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 udata ->
          getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 Bv ->
          getr regs 21 = Z_to_bv 64 Tv -> getr regs 26 = Z_to_bv 64 4294967295 ->
          MI m -> Z.of_nat q * Bv <= n < (Z.of_nat q + 1) * Bv ->
          exists r m', msteps RSEGS (mkst regs (0x143e0 : word) m rom) (mkst r (0x14424 : word) m' rom)
            /\ MI m' /\ lkeeps hk regs r
            /\ getr r 11 = Z_to_bv 64 (Z.of_nat q * Bv)
            /\ getr r 10 = Z_to_bv 64 (adler_spec 1 (DD (Z.of_nat q * Bv)))
            /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
            /\ getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 21 = Z_to_bv 64 Tv
            /\ getr r 26 = Z_to_bv 64 4294967295.
        Proof.
          intros regs m q R2 R8 R9 R18 R19 R20 R21 R26 HM Hq.
          ranges. pose proof (Bv_range mem data Bv HBv) as HB'.
          pose proof (harness_adler_init) as HI. rewrite <- (D_nil mem data) in HI.
          destruct q as [|k].
          -
            change (Z.of_nat 0) with 0 in *. rewrite Z.mul_0_l in *.
            assert (S : exists r, msteps RSEGS (mkst regs (0x143e0 : word) m rom) (mkst r (0x14424 : word) m rom)
              /\ getr r 11 = Z_to_bv 64 0 /\ getr r 10 = Z_to_bv 64 1
              /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata
              /\ getr r 18 = Z_to_bv 64 1 /\ getr r 19 = Z_to_bv 64 n /\ getr r 21 = Z_to_bv 64 Tv
              /\ getr r 26 = Z_to_bv 64 4294967295
              /\ lkeeps hk regs r).
            { eexists. split.
              - stepb_ft F_14380 D_14380 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_lt; lia).
                stepz F_14384 D_14384. stepz F_14388 D_14388. stepz F_1438c D_1438c.
                apply mst_refl.
              - post. }
            destruct S as (r & M & V11 & V10 & V2 & V8 & V9 & V18 & V19 & V21 & V26 & K).
            exists r, m. rewrite HI. split; [exact M|]. split; [exact HM|]. split; [exact K|].
            repeat split; assumption.
          -
            assert (Hk : 0 + Bv + Z.of_nat k * Bv <= n < 0 + Bv + (Z.of_nat k + 1) * Bv)
              by (rewrite Nat2Z.inj_succ in Hq; lia).
            assert (S : exists r, msteps RSEGS (mkst regs (0x143e0 : word) m rom) (mkst r (0x143f8 : word) m rom)
              /\ ADH r 0 1 /\ lkeeps hk regs r).
            { eexists. split.
              - stepb_tk F_14380 D_14380 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
                stepz F_14390 D_14390. stepz F_14394 D_14394.
                apply mst_refl.
              - unfold ADH. post. }
            destruct S as (r0 & MS0 & HA0 & K0).
            destruct (adl_iter r0 m 0 1 HA0 HM ltac:(lia) ltac:(lia) (eq_sym HI)) as (r1 & m1 & M1 & HP1 & HM1 & K1).
            destruct (adl_loop k r1 m1 (0 + Bv) HP1 HM1 ltac:(lia) Hk)
              as (r & m' & M & HM' & K & V11 & V10 & V2 & V8 & V9 & V18 & V19 & V21 & V26).
            exists r, m'. replace (Z.of_nat (S k) * Bv) with (0 + Bv + Z.of_nat k * Bv) by lia.
            split.
            { eapply msteps_trans; [exact MS0|]. eapply msteps_trans; [exact M1 | exact M]. }
            split; [exact HM'|].
            split; [eapply lkeeps_trans; [exact K0|]; eapply lkeeps_trans; [exact K1 | exact K]|].
            repeat split; assumption.
        Qed.
      End LOOPA.

      Lemma phase3b : forall regs m offq A,
        getr regs 10 = Z_to_bv 64 A -> getr regs 11 = Z_to_bv 64 offq ->
        getr regs 2 = Z_to_bv 64 (usp - 112) -> getr regs 8 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 udata ->
        getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 n -> getr regs 21 = Z_to_bv 64 (n - offq) ->
        getr regs 26 = Z_to_bv 64 4294967295 ->
        MI m -> 0 <= offq <= n -> A = adler_spec 1 (DD offq) ->
        exists r m', msteps RSEGS (mkst regs (0x14424 : word) m rom) (mkst r (0x14480 : word) m' rom)
          /\ MI m' /\ lkeeps hk regs r /\ getr r 2 = Z_to_bv 64 (usp - 112).
      Proof.
        intros regs m offq A R10 R11 R2 R8 R9 R18 R19 R21 R26 HM Hoff HA.
        ranges. minvs.
        assert (HAr : 0 <= A < two32) by (rewrite HA; apply adler_spec_1_range).
        set (T := n - offq) in *.
        assert (S1 : exists r, msteps RSEGS (mkst regs (0x14424 : word) m rom) (mkst r (0x14e14 : word) m rom)
          /\ getr r 1 = (0x14434%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
          /\ getr r 10 = Z_to_bv 64 A /\ getr r 11 = Z_to_bv 64 (udata + offq) /\ getr r 12 = Z_to_bv 64 T
          /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
          /\ getr r 19 = Z_to_bv 64 n /\ getr r 26 = Z_to_bv 64 4294967295
          /\ lkeeps hk regs r).
        { eexists. split.
          - stepz F_143c4 D_143c4. rewrite <- (mod32_land A), (mod_small_32 A) by lia.
            stepz F_143c8 D_143c8. stepz F_143cc D_143cc. stepz F_143d0 D_143d0.
            apply mst_refl.
          - post. }
        destruct S1 as (r1 & M1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A26 & K1).
        destruct (s0_adler32_z r1 m rom (0x14434%bv : word) (usp - 112) A (udata + offq) T
                    A1 ltac:(retok) A2 A10 A11 A12
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(apply (Mstk m); [exact HM | lia | change (Z.of_nat 32) with 32; lia])
                    ltac:(intros _; lia) ltac:(apply Mimg; exact HM)
                    ltac:(apply (Mrdo m offq T HM); lia))
          as (r2 & m2 & M2 & V2 & K2 & F2).
        rewrite (Mbytes m offq T HM) in V2 by lia.
        change (bytes_at RSEGS mem (udata + offq) (Z.to_nat T)) with (CC offq T) in V2.
        assert (EADL : adler32_z_model A (CC offq T) = adler_spec 1 (DD n)).
        { rewrite HA. replace (DD n) with (DD (offq + T)) by (f_equal; lia). rewrite D_CH by lia.
          apply harness_adler_stream; [apply D_bytes | apply CH_bytes]. }
        rewrite EADL in V2. set (ADL := adler_spec 1 (DD n)) in V2.
        assert (HADL : 0 <= ADL < two32) by (subst ADL; apply adler_spec_1_range).
        pose proof (sx32_range ADL HADL) as HsxA.
        assert (HM2 : MI m2) by (eapply (Mframe m m2); [exact HM | exact F2 | lia | lia | lia]).
        xfer K2 A2 B2. xfer K2 A8 B8. xfer K2 A9 B9. xfer K2 A18 B18. xfer K2 A19 B19. xfer K2 A26 B26.
        assert (S3 : exists r, msteps RSEGS (mkst r2 (0x14434%bv : word) m2 rom) (mkst r (0x151d8 : word) m2 rom)
          /\ getr r 1 = (0x1444c%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
          /\ getr r 10 = Z_to_bv 64 1 /\ getr r 11 = Z_to_bv 64 udata /\ getr r 12 = Z_to_bv 64 n
          /\ getr r 20 = Z_to_bv 64 ADL /\ getr r 21 = Z_to_bv 64 (sx32 ADL)
          /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = Z_to_bv 64 udata /\ getr r 18 = Z_to_bv 64 1
          /\ getr r 19 = Z_to_bv 64 n /\ getr r 26 = Z_to_bv 64 4294967295
          /\ lkeeps hk r2 r).
        { eexists. split.
          - stepz F_143d4 D_143d4. stepz F_143d8 D_143d8. rewrite (mod_small_32 ADL) by lia.
            stepz F_143dc D_143dc. stepz F_143e0 D_143e0. stepz F_143e4 D_143e4. stepz F_143e8 D_143e8.
            apply mst_refl.
          - post. }
        destruct S3 as (r3 & M3 & B1 & B2' & B10 & B11 & B12 & B20 & B21 & B8' & B9' & B18' & B19' & B26' & K3).
        destruct (s0_adler32 r3 m2 rom (0x1444c%bv : word) (usp - 112) 1 udata n n
                    B1 ltac:(retok) B2' B10 B11 B12
                    ltac:(lia) ltac:(rewrite Z.mod_small; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(apply (Mstk m2); [exact HM2 | lia | change (Z.of_nat 32) with 32; lia])
                    ltac:(intros _; lia) ltac:(apply Mimg; exact HM2)
                    (Mrd m2 HM2))
          as (r4 & m4 & M4 & V4 & K4 & F4).
        rewrite <- (Z.add_0_r udata) in V4. rewrite (Mbytes m2 0 n HM2) in V4 by lia.
        rewrite (Z.add_0_r udata) in V4. change (bytes_at RSEGS mem udata (Z.to_nat n)) with (DD n) in V4.
        pose proof (harness_adler_whole (DD n) (D_bytes mem data n)) as EW. unfold adler32_model in EW.
        rewrite EW in V4. fold ADL in V4.
        assert (HM4 : MI m4) by (eapply (Mframe m2 m4); [exact HM2 | exact F4 | lia | lia | lia]).
        xfer K4 B2' C2. xfer K4 B8' C8. xfer K4 B9' C9. xfer K4 B18' C18. xfer K4 B19' C19.
        xfer K4 B20 C20. xfer K4 B21 C21. xfer K4 B26' C26.
        assert (S5 : exists r, msteps RSEGS (mkst r4 (0x1444c%bv : word) m4 rom) (mkst r (0x151e4 : word) m4 rom)
          /\ getr r 1 = (0x14468%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
          /\ getr r 10 = Z_to_bv 64 ADL /\ getr r 11 = Z_to_bv 64 ADL /\ getr r 12 = Z_to_bv 64 n
          /\ getr r 9 = Z_to_bv 64 ADL /\ getr r 8 = Z_to_bv 64 n
          /\ getr r 19 = Z_to_bv 64 n /\ getr r 26 = Z_to_bv 64 4294967295
          /\ lkeeps hk r4 r).
        { eexists. split.
          - stepz F_143ec D_143ec. rewrite (mod_small_32 ADL) by lia.
            stepb_ft F_143f0 D_143f0 ltac:(rwR; apply c_eq_refl).
            stepz F_143f4 D_143f4. rewrite <- (mod32_land ADL), (mod_small_32 ADL) by lia.
            stepz F_143f8 D_143f8. rewrite <- (mod32_land ADL), (mod_small_32 ADL) by lia.
            stepz F_143fc D_143fc. stepz F_14400 D_14400. stepz F_14404 D_14404.
            apply mst_refl.
          - post. }
        destruct S5 as (r5 & M5 & C1 & D2 & D10 & D11 & D12 & D9 & D8 & D19 & D26 & K5).
        destruct (s0_adler32_combine r5 m4 rom (0x14468%bv : word) ADL ADL n C1 ltac:(retok) D10 D11 D12
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply Mimg; exact HM4)) as (r6 & M6 & V6 & K6).
        set (CMB := adler32_combine_model ADL ADL n) in V6.
        xfer K6 D2 E2. xfer K6 D8 E8. xfer K6 D9 E9. xfer K6 D19 E19. xfer K6 D26 E26.
        assert (S7 : exists r, msteps RSEGS (mkst r6 (0x14468%bv : word) m4 rom) (mkst r (0x151e4 : word) m4 rom)
          /\ getr r 1 = (0x1447c%bv : word) /\ getr r 2 = Z_to_bv 64 (usp - 112)
          /\ getr r 10 = Z_to_bv 64 ADL /\ getr r 11 = Z_to_bv 64 ADL /\ getr r 12 = Z_to_bv 64 n
          /\ getr r 18 = Z_to_bv 64 CMB
          /\ lkeeps hk r6 r).
        { eexists. split.
          - stepz F_14408 D_14408. stepz F_1440c D_1440c. stepz F_14410 D_14410. stepz F_14414 D_14414.
            stepz F_14418 D_14418. apply mst_refl.
          - post. }
        destruct S7 as (r7 & M7 & E1 & F2' & F10 & F11 & F12 & F18 & K7).
        destruct (s0_adler32_combine r7 m4 rom (0x1447c%bv : word) ADL ADL n E1 ltac:(retok) F10 F11 F12
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply Mimg; exact HM4)) as (r8 & M8 & V8 & K8).
        fold CMB in V8.
        xfer K8 F2' G2. xfer K8 F18 G18.
        assert (S9 : exists r, msteps RSEGS (mkst r8 (0x1447c%bv : word) m4 rom) (mkst r (0x14480 : word) m4 rom)
          /\ getr r 2 = Z_to_bv 64 (usp - 112) /\ lkeeps hk r8 r).
        { eexists. split.
          - stepb_ft F_1441c D_1441c ltac:(rwR; apply c_eq_refl). apply mst_refl.
          - post. }
        destruct S9 as (r9 & M9 & X2 & K9).
        exists r9, m4. split.
        { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
          eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6|].
          eapply msteps_trans; [exact M7|]. eapply msteps_trans; [exact M8|]. exact M9. }
        split; [exact HM4|]. split; [|exact X2].
        intros x Hx.
        rewrite (K9 x Hx). rewrite (K8 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K7 x Hx).
        rewrite (K6 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K5 x Hx).
        rewrite (K4 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K3 x Hx).
        rewrite (K2 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx).
      Qed.
    End WithM0.

    Lemma fuzz_main : forall regs,
      getr regs 1 = ret -> getr regs 2 = sp -> getr regs 10 = data -> getr regs 11 = Z_to_bv 64 n ->
      exists regs' mem',
        msteps RSEGS (mkst regs (0x141f0 : word) mem rom) (mkst regs' ret mem' rom)
        /\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 0 /\ frame_mod mem mem' (FRR sp).
    Proof.
      intros regs R1 R2 R10 R11. ranges.
      assert (R2' : getr regs 2 = Z_to_bv 64 usp) by (rewrite R2; apply word_zv).
      set (M := M13r regs).
      pose proof (M13_frame mem sp Hsp regs) as HMf. fold M in HMf.
      pose proof (M13_img regs data n HF) as HMi. fold M in HMi.
      pose proof (minv_M0 sp M HMi) as HM.
      destruct (prologue_run mem sp rom Hsp Hstk regs data n R2' R10 R11)
        as (r1 & M1 & P1 & P2 & P8 & P9 & P10 & P11 & P12 & K1). fold M in M1.
      destruct (s0_crc32_null r1 M rom (0x14240%bv : word) P1 ltac:(retok) P11) as (r2 & M2 & V2 & K2).
      xfer K2 P2 Q2. xfer K2 P8 Q8. xfer K2 P9 Q9.
      destruct (segB rom r2 M V2) as (r3 & M3 & A1 & A19 & A10 & A11 & A12 & A2 & A8 & A9 & K3).
      rewrite Q2 in A2. rewrite Q8 in A8. rewrite Q9 in A9.
      destruct (s0_adler32_null r3 M rom (0x14254%bv : word) A1 ltac:(retok) A11 A12) as (r4 & M4 & V4 & K4).
      xfer K4 A2 B2. xfer K4 A8 B8. xfer K4 A9 B9. xfer K4 A19 B19.
      assert (B9' : getr r4 9 = Z_to_bv 64 udata) by (rewrite B9; apply word_zv).
      destruct (Frd _ _ _ _ HF 0 ltac:(lia)) as [bb Hbb]. rewrite Z.add_0_r in Hbb.
      assert (Hb0 : bv_unsigned bb = b0 mem data) by (unfold b0; symmetry; exact (byte_at_rdn RSEGS mem udata bb Hbb)).
      assert (Hbb' : rdn RSEGS M (Z_to_bv 64 udata) 1 = Some [bb]).
      { rewrite <- Hbb. apply (frame_mod_rdn RSEGS mem M (FRR sp) 1 (Z_to_bv 64 udata) HMf).
        - intros i Hi. cbn [outside FRR]. split; [|exact I]. unfold in_rng, FR.
          rewrite (u64_lit udata) by lia. rewrite !u64_lit by lia. lia.
        - rewrite u64_lit by lia. change (Z.of_nat 1) with 1. lia. }
      remember (B mem data) as Bv eqn:HBv.
      destruct (segC mem sp rom data n HF r4 M bb Bv V4 B8 B9' B19 Hbb' Hb0 HBv)
        as (r5 & M5 & C1 & C10 & C18 & C20 & C22 & C26 & C2 & C8 & C9 & K5).
      rewrite B2 in C2.
      destruct (gen_run M rom (0x1428c%bv : word) ltac:(retok) HMi r5 Bv C1 C10 ltac:(lia)) as (r6 & M6 & V6 & K6).
      rewrite (gen_fold Bv ltac:(lia)) in V6. remember (crc32_combine_gen Bv) as OPv eqn:HOPv.
      pose proof (OPv_range Bv OPv HOPv) as HOPr.
      xfer K6 C2 D2'. xfer K6 C8 D8. xfer K6 C9 D9. xfer K6 C18 D18. xfer K6 C20 D20. xfer K6 C22 D22. xfer K6 C26 D26.
      destruct (segD mem sp rom data n HF r6 M OPv V6 D8 D22 HOPr)
        as (r7 & M7 & E25 & E21 & E19 & E23 & E2 & E8 & E9 & E18 & E20 & E22 & E26 & K7).
      rewrite D2' in E2. rewrite D9 in E9. rewrite D18 in E18. rewrite D20 in E20. rewrite D26 in E26.
      remember (Z.to_nat (n / Bv)) as k eqn:Hkdef.
      assert (Hk : Z.of_nat k = n / Bv) by (rewrite Hkdef, Z2Nat.id; [reflexivity | apply Z.div_pos; lia]).
      destruct (chunk_arith n Bv (Z.of_nat k) ltac:(lia) ltac:(lia) Hk) as (Hkb & Hmod & Hk0).
      pose proof harness_crc_init as HCI. rewrite <- (D_nil mem data) in HCI.
      assert (HCRH : CRH sp data n Bv OPv r7 0 (crc32_spec 0 (DD 0))).
      { rewrite HCI. unfold CRH. repeat split; assumption. }
      destruct (crc_loop mem sp rom Hsp Hstk data n HF Hapart s0_crc32_z M HMf Bv OPv HBv HOPv k r7 M 0 HCRH HM ltac:(lia) Hkb)
        as (r8 & m8 & M8 & HM8 & K8 & F10 & F23 & F2 & F8 & F9 & F18 & F19 & F20 & F22 & F26).
      rewrite Z.add_0_l in F10, F23.
      assert (Hoffq : 0 <= Z.of_nat k * Bv <= n) by lia.
      destruct (phase2 mem sp rom Hsp Hstk data n HF Hapart s0_crc32_z s0_crc32 M HMf Bv HBv r8 m8 (Z.of_nat k * Bv)
                  F10 F23 F2 F8 F9 F18 F19 F20 F22 F26 HM8 Hoffq ltac:(lia) Hmod)
        as (r9 & m9 & M9 & HM9 & K9 & G2 & G8 & G9 & G18 & G19 & G20 & G21 & G26).
      destruct (phase3a M HMf Bv (n - Z.of_nat k * Bv) HBv r9 m9 k G2 G8 G9 G18 G19 G20 G21 G26 HM9 ltac:(lia))
        as (r10 & m10 & M10 & HM10 & K10 & I11 & I10 & I2 & I8 & I9 & I18 & I19 & I21 & I26).
      destruct (phase3b M HMf r10 m10 (Z.of_nat k * Bv) _ I10 I11 I2 I8 I9 I18 I19 I21 I26 HM10 Hoffq eq_refl)
        as (r11 & m11 & M11 & HM11 & K11 & J2).
      pose proof (M13_slots regs) as (E1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27).
      fold M in E1, S8, S9, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27.
      pose proof (minv_slot mem sp Hsp data n HF Hapart M m11) as SL.
      destruct (epilogue_run sp ret rom Hret r11 m11 (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)
                  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
                  (getr regs 25) (getr regs 26) (getr regs 27) J2 R1
                  ltac:(rewrite (SL _ HM11) by lia; exact E1) ltac:(rewrite (SL _ HM11) by lia; exact S8)
                  ltac:(rewrite (SL _ HM11) by lia; exact S9) ltac:(rewrite (SL _ HM11) by lia; exact S18)
                  ltac:(rewrite (SL _ HM11) by lia; exact S19) ltac:(rewrite (SL _ HM11) by lia; exact S20)
                  ltac:(rewrite (SL _ HM11) by lia; exact S21) ltac:(rewrite (SL _ HM11) by lia; exact S22)
                  ltac:(rewrite (SL _ HM11) by lia; exact S23) ltac:(rewrite (SL _ HM11) by lia; exact S24)
                  ltac:(rewrite (SL _ HM11) by lia; exact S25) ltac:(rewrite (SL _ HM11) by lia; exact S26)
                  ltac:(rewrite (SL _ HM11) by lia; exact S27))
        as (r12 & M12 & Q10 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & K12).
      exists r12, m11. split; [|split; [|split]].
      - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
        eapply msteps_trans; [exact M4|]. eapply msteps_trans; [exact M5|]. eapply msteps_trans; [exact M6|].
        eapply msteps_trans; [exact M7|]. eapply msteps_trans; [exact M8|]. eapply msteps_trans; [exact M9|].
        eapply msteps_trans; [exact M10|]. eapply msteps_trans; [exact M11|]. exact M12.
      - apply keeps_cs_of; try assumption.
        + intros x Hx.
          rewrite (K12 x Hx). rewrite (K11 x Hx). rewrite (K10 x Hx). rewrite (K9 x Hx). rewrite (K8 x Hx).
          rewrite (K7 x Hx). rewrite (K6 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K5 x Hx).
          rewrite (K4 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). rewrite (K3 x Hx).
          rewrite (K2 x) by (revert Hx; cbv; (first [solve [liafast_keep_section; tauto] | tauto])). apply (K1 x Hx).
        + rewrite Z2, R2. symmetry. apply word_zv.
      - exact Q10.
      - destruct HM11 as [Hf11 _].
        eapply frame_mod_trans_same; [exact HMf|].
        eapply frame_mod_weaken; [| exact Hf11].
        intros a [Ha _]. cbn [outside R80]. split; [|exact I].
        unfold R80, FRR, FR, in_rng in *. rewrite !u64_lit in Ha |- * by lia. lia.
    Qed.
  End InRange.
End MAIN.


Theorem s0_fuzz : s0_fuzz_stmt.
Proof.
  intros regs mem rom ret sp data n R1 Hret R2 R10 R11 Hn Hdata Hnw Hsp Hrd Hstk Hapart Himg.
  pose proof (u64_range data).
  assert (Hnr : 0 <= n < 2 ^ 64) by lia.
  change [(Z_to_bv 64 (bv_unsigned sp - 192), 192%Z)] with (FRR sp).
  destruct (Z.le_gt_cases 1 n) as [H1|H1]; [destruct (Z.le_gt_cases n 1048576) as [H2|H2]|].
  -
    assert (HC : fzH mem sp data n).
    { constructor.
      - lia.
      - exact Hdata.
      - exact Hnw.
      - unfold FR; lia.
      - intros i Hi. exact (Hrd ltac:(lia) i Hi).
      - exact Hstk.
      - apply img_ok_of_hyp. exact Himg. }
    exact (fuzz_main mem sp ret rom Hret Hsp Hstk data n HC ltac:(apply Hapart; lia) regs R1 R2 R10 R11).
  - apply (fuzz_trivial mem sp ret rom Hret Hsp Hstk regs n R1 R2 R11); lia.
  - apply (fuzz_trivial mem sp ret rom Hret Hsp Hstk regs n R1 R2 R11); lia.
Qed.
End FXG.
