(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk S0FuzzBase S0Fuzz_code S0FuzzIface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathAdler.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition NEGB : Z := 18446744073709486095.

Section PURE.
  Variables (adler1 adler2 len2 : Z).

  Definition lo1 : Z := Z.land adler1 65535.
  Definition lo2 : Z := Z.land adler2 65535.
  Definition hi1 : Z := Z.shiftr (adler1 mod two32) 16.
  Definition hi2 : Z := Z.shiftr (adler2 mod two32) 16.
  Definition q0 : Z := len2 * AMAGIC / two64.
  Definition tq : Z := Z.shiftr (len2 - q0) 1 + q0.
  Definition qq : Z := Z.shiftr tq 15.
  Definition rem : Z := len2 - qq * 65521.
  Definition pr : Z := rem * lo1.
  Definition q2 : Z := Z.shiftr (pr * 2147975281) 47.
  Definition s2m : Z := pr - q2 * 65521.
  Definition S1 : Z := lo1 + lo2 + 65535 - 15.
  Definition S2 : Z := hi1 + hi2 + 65535 - rem + s2m - 14.
  Definition c1 : Z := if 65520 <? S1 then S1 - 65521 else S1.
  Definition f1 : Z := if 65520 <? c1 then c1 - 65521 else c1.
  Definition c2 : Z := if 131041 <? S2 then S2 - 131042 else S2.
  Definition f2 : Z := if 65520 <? c2 then c2 - 65521 else c2.
  Definition adlc_val : Z := Z.lor (f2 * 2 ^ 16) f1.

  Lemma lo1_range : 0 <= lo1 <= 65535.  Proof. unfold lo1. apply land_range. lia. Qed.
  Lemma lo2_range : 0 <= lo2 <= 65535.  Proof. unfold lo2. apply land_range. lia. Qed.
  Lemma hi1_range : 0 <= hi1 < 65536.
  Proof.
    unfold hi1. pose proof (mod32_range adler1).
    apply (shiftr_range _ 16 16); [lia|lia|]. change (2 ^ (16 + 16)) with two32. lia.
  Qed.
  Lemma hi2_range : 0 <= hi2 < 65536.
  Proof.
    unfold hi2. pose proof (mod32_range adler2).
    apply (shiftr_range _ 16 16); [lia|lia|]. change (2 ^ (16 + 16)) with two32. lia.
  Qed.

  Section HYPS.
  Hypothesis Ha1 : 0 <= adler1 < two64.
  Hypothesis Hn : 0 <= len2 < 9223372036854775808.

  Lemma qq_val : qq = len2 / BASE.
  Proof.
    clear Ha1. unfold qq, tq, q0. change two64 with (2 ^ 64). apply adler_magic_div. lia.
  Qed.

  Lemma rem_val : rem = len2 mod BASE.
  Proof. clear Ha1. unfold rem. rewrite qq_val. change 65521 with BASE. apply mod_BASE_sub. Qed.

  Lemma rem_range : 0 <= rem < 65521.
  Proof. clear Ha1. rewrite rem_val. apply Z.mod_pos_bound. unfold BASE. lia. Qed.

  Lemma pr_range : 0 <= pr < 65521 * 65536.
  Proof. unfold pr. pose proof rem_range. pose proof lo1_range. clear Ha1 Hn. nia. Qed.

  Lemma q2_val : q2 = pr / BASE.
  Proof. unfold q2. change 2147975281 with AMAGIC2. apply adler_magic2_div. pose proof pr_range. lia. Qed.

  Lemma s2m_val : s2m = pr mod BASE.
  Proof. unfold s2m. rewrite q2_val. change 65521 with BASE. apply mod_BASE_sub. Qed.

  Lemma s2m_range : 0 <= s2m < 65521.
  Proof. rewrite s2m_val. apply Z.mod_pos_bound. unfold BASE. lia. Qed.

  Lemma q0_le : 0 <= q0 <= len2.
  Proof.
    clear Ha1. unfold q0. pose proof (adler_magic_ranges len2 ltac:(lia)) as R. cbv zeta in R.
    change two64 with (2 ^ 64). lia.
  Qed.
  Lemma tq_range : 0 <= tq < two64.
  Proof.
    clear Ha1. unfold tq, q0. pose proof (adler_magic_ranges len2 ltac:(lia)) as R. cbv zeta in R.
    change two64 with (2 ^ 64). lia.
  Qed.
  Lemma qq_range : 0 <= qq <= len2 /\ 0 <= qq * 65521 <= len2.
  Proof.
    clear Ha1. rewrite qq_val. pose proof (adler_magic_ranges len2 ltac:(lia)) as R. cbv zeta in R. unfold BASE in *. lia.
  Qed.
  Lemma prA_range : 0 <= pr * 2147975281 < two64.
  Proof. pose proof pr_range. clear Ha1 Hn. nia. Qed.
  Lemma q2_range : 0 <= q2 * 65521 <= pr.
  Proof.
    rewrite q2_val. pose proof pr_range. unfold BASE.
    split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia] |].
    rewrite Z.mul_comm. apply Z.mul_div_le. lia.
  Qed.

  Lemma hi_land : forall a, 0 <= a -> Z.shiftr (a mod two32) 16 = Z.land (Z.shiftr a 16) 65535.
  Proof.
    intros a Ha. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
    rewrite !Z.shiftr_div_pow2 by lia. change two32 with (2 ^ 16 * 2 ^ 16).
    rewrite Z.rem_mul_r by lia.
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia.
    rewrite (Z.div_small (a mod 2 ^ 16)) by (apply Z.mod_pos_bound; lia). lia.
  Qed.

  Lemma csub_if : forall x, csub x = (if 65520 <? x then x - 65521 else x).
  Proof. intros x. unfold csub, BASE. destruct (Z.leb_spec 65521 x), (Z.ltb_spec 65520 x); lia. Qed.

  Lemma csub2_if : forall x, (if 2 * BASE <=? x then x - 2 * BASE else x) = (if 131041 <? x then x - 131042 else x).
  Proof. intros x. unfold BASE. destruct (Z.leb_spec (2 * 65521) x), (Z.ltb_spec 131041 x); lia. Qed.

  Theorem adlc_val_model : 0 <= adler2 -> adlc_val = adler32_combine_model adler1 adler2 len2.
  Proof.
    intros Ha2.
    unfold adler32_combine_model.
    destruct (Z.ltb_spec len2 0); [lia|].
    cbv zeta. rewrite <- rem_val.
    rewrite <- (hi_land adler1), <- (hi_land adler2) by lia.
    change (Z.land adler1 65535) with lo1. change (Z.land adler2 65535) with lo2.
    change (Z.shiftr (adler1 mod two32) 16) with hi1. change (Z.shiftr (adler2 mod two32) 16) with hi2.
    change (rem * lo1) with pr. rewrite <- s2m_val.
    rewrite !csub_if, csub2_if.
    unfold adlc_val, adler_comb, f1, c1, f2, c2, S1, S2.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. unfold BASE.
    replace (lo1 + (lo2 + 65521 - 1)) with (lo1 + lo2 + 65535 - 15) by lia.
    replace (s2m + (hi1 + hi2 + 65521 - rem)) with (hi1 + hi2 + 65535 - rem + s2m - 14) by lia.
    reflexivity.
  Qed.
  End HYPS.
End PURE.

Lemma zv_add_wrap : forall X L k, (L + k) mod two64 = 0 -> Z_to_bv 64 (X + L) = Z_to_bv 64 (X - k).
Proof.
  intros X L k H. apply zv_eq. replace (X + L) with ((X - k) + (L + k)) by lia.
  rewrite Z.add_mod, H, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.

Lemma csel_lemma : forall C (c : bool) L k, (L + k) mod two64 = 0 ->
  Z_to_bv 64 (C + Z.land (0 - (if c then 1 else 0)) L) = Z_to_bv 64 (if c then C - k else C).
Proof.
  intros C c L k H. destruct c.
  - change (0 - 1) with (-1). rewrite Z.land_m1_l. apply zv_add_wrap. exact H.
  - change (0 - 0) with 0. rewrite Z.land_0_l, Z.add_0_r. reflexivity.
Qed.

Section ADLC.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (retw : word).
  Hypothesis Hret : ret_ok retw.
  Hypothesis Himg : img_ok m.

  Ltac solve_cs := apply (proj2 (keeps_cs_lkeeps _ _)); solve_lkeeps.
  Ltac post := repeat split; gres; rwR;
    first [ reflexivity | assumption | lia | solve_cs ].
  Ltac fix_auipc := match goal with |- context [regupd _ _ (v_auipc ?p ?i)] => wlit_closed (v_auipc p i) end.
  Ltac addr_fold := match goal with |- rdn _ _ (Z_to_bv 64 ?e) _ = _ => let v := eval cbv in e in change e with v end.

  Lemma adlc_A : forall regs (a1 a2 n : Z),
    getr regs 10 = Z_to_bv 64 a1 -> getr regs 11 = Z_to_bv 64 a2 -> getr regs 12 = Z_to_bv 64 n ->
    0 <= a1 < two64 -> 0 <= a2 < two64 -> 0 <= n < 9223372036854775808 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x151e4 : word) m rom) (mkst r (0x15224 : word) m rom)
      /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 10 = Z_to_bv 64 (q0 n)
      /\ getr r 14 = Z_to_bv 64 65536
      /\ getr r 15 = Z_to_bv 64 268496896
      /\ getr r 16 = Z_to_bv 64 (hi1 a1 + hi2 a2 + 65535)
      /\ getr r 17 = Z_to_bv 64 (lo1 a1 + lo2 a2 + 65535)
      /\ getr r 5 = Z_to_bv 64 18446744073709486080
      /\ getr r 6 = Z_to_bv 64 (lo1 a1)
      /\ getr r 1 = getr regs 1
      /\ keeps_cs regs r.
  Proof.
    intros regs a1 a2 n R10 R11 R12 Ha1 Ha2 Hn.
    assert (HM : 0 <= AMAGIC < two64) by (unfold AMAGIC; lia).
    eexists. split.
    - stepb_ft F_15138 D_15138 ltac:(rwR; apply zc_lts_0_false; lia).
      stepz F_1513c D_1513c. fix_auipc. stepz F_15140 D_15140. stepz F_15144 D_15144.
      stepz F_15148 D_15148. stepz F_1514c D_1514c. stepz F_15150 D_15150.
      chain_step;
      [ reflexivity
      | eapply step_ld with (v := Z_to_bv 64 AMAGIC);
        [ exact F_15154 | reflexivity | exact D_15154
        | gres; imm_norm; rewrite zv_addi; addr_fold; apply rd_amag; exact Himg
        | apply amag_bs_v ]
      | step_simpl; gres ].
      stepz F_15158 D_15158. stepz F_1515c D_1515c. stepz F_15160 D_15160. stepz F_15164 D_15164.
      stepz F_15168 D_15168. stepz F_1516c D_1516c. stepz F_15170 D_15170.
      stepi F_15174 D_15174; znorm. zval (n * AMAGIC / two64) ltac:(apply zv_mulhu; lia).
      apply mst_refl.
    - unfold q0, hi1, hi2, lo1, lo2. post.
  Qed.

  Section ARGS.
    Variables (av1 av2 n : Z).
    Hypothesis Ha1 : 0 <= av1 < two64.
    Hypothesis Ha2 : 0 <= av2 < two64.
    Hypothesis Hn : 0 <= n < 9223372036854775808.

    Lemma adlc_B : forall regs,
      getr regs 12 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 (q0 n) -> getr regs 14 = Z_to_bv 64 65536 ->
      getr regs 15 = Z_to_bv 64 268496896 -> getr regs 16 = Z_to_bv 64 (hi1 av1 + hi2 av2 + 65535) ->
      getr regs 17 = Z_to_bv 64 (lo1 av1 + lo2 av2 + 65535) -> getr regs 5 = Z_to_bv 64 18446744073709486080 ->
      getr regs 6 = Z_to_bv 64 (lo1 av1) ->
      exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x15224 : word) m rom) (mkst r (0x1527c : word) m rom)
        /\ getr r 10 = Z_to_bv 64 65520
        /\ getr r 13 = Z_to_bv 64 (S1 av1 av2)
        /\ getr r 11 = Z_to_bv 64 (S2 av1 av2 n)
        /\ getr r 12 = Z_to_bv 64 NEGB
        /\ getr r 1 = getr regs 1
        /\ keeps_cs regs r.
    Proof.
      intros regs R12 R10 R14 R15 R16 R17 R5 R6.
      pose proof (q0_le n Hn) as Hq0. pose proof (tq_range n Hn) as Htq. pose proof (qq_range n Hn) as Hqq.
      pose proof (prA_range av1 n Hn) as HprA. pose proof (q2_range av1 n Hn) as Hq2.
      pose proof (pr_range av1 n Hn) as Hpr. pose proof (s2m_range av1 n Hn) as Hs2m.
      pose proof (lo1_range av1) as Hl1. pose proof (lo2_range av2) as Hl2.
      pose proof (hi1_range av1) as Hh1. pose proof (hi2_range av2) as Hh2. pose proof (rem_range n Hn) as Hrem.
      eexists. split.
      - stepz F_15178 D_15178.
        stepi F_1517c D_1517c; znorm. zval (Z.shiftr (n - q0 n) 1) ltac:(apply zv_srli; lia).
        stepz F_15180 D_15180. change (Z.shiftr (n - q0 n) 1 + q0 n) with (tq n).
        stepz F_15184 D_15184. stepz F_15188 D_15188. stepz F_1518c D_1518c. stepz F_15190 D_15190.
        stepz F_15194 D_15194.
        stepi F_15198 D_15198; znorm. zval (Z.shiftr (tq n) 15) ltac:(apply zv_srli; lia).
        change (Z.shiftr (tq n) 15) with (qq n).
        stepz F_1519c D_1519c. stepz F_151a0 D_151a0. change (n - qq n * 65521) with (rem n).
        stepz F_151a4 D_151a4. change (rem n * lo1 av1) with (pr av1 n).
        stepz F_151a8 D_151a8. stepz F_151ac D_151ac.
        stepi F_151b0 D_151b0; znorm. zval (Z.shiftr (pr av1 n * 2147975281) 47) ltac:(apply zv_srli; lia).
        change (Z.shiftr (pr av1 n * 2147975281) 47) with (q2 av1 n).
        stepz F_151b4 D_151b4. stepz F_151b8 D_151b8.
        change (pr av1 n - q2 av1 n * 65521) with (s2m av1 n).
        zval (s2m av1 n) ltac:(rewrite (mod_small_32 (s2m av1 n)), sx32_small by lia; reflexivity).
        stepz F_151bc D_151bc. stepz F_151c0 D_151c0.
        zval (s2m av1 n) ltac:(rewrite (mod_small_32 (s2m av1 n)) by lia; reflexivity).
        stepz F_151c4 D_151c4. stepz F_151c8 D_151c8. stepz F_151cc D_151cc.
        apply mst_refl.
      - unfold S1, S2, NEGB. post.
    Qed.

    Lemma adlc_C : forall regs (S1v : Z),
      getr regs 10 = Z_to_bv 64 65520 -> getr regs 13 = Z_to_bv 64 S1v -> getr regs 12 = Z_to_bv 64 NEGB ->
      65520 <= S1v < two32 ->
      exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1527c : word) m rom) (mkst r (0x15298 : word) m rom)
        /\ getr r 13 = Z_to_bv 64 (if 65520 <? S1v then S1v - 65521 else S1v)
        /\ getr r 10 = Z_to_bv 64 65520 /\ getr r 12 = Z_to_bv 64 NEGB
        /\ getr r 11 = getr regs 11 /\ getr r 1 = getr regs 1
        /\ keeps_cs regs r.
    Proof.
      intros regs S1v R10 R13 R12 HS1.
      destruct (Z.ltb_spec 65520 S1v).
      - eexists. split; [|split].
        + stepb_tk F_151d0 D_151d0 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_lt; lia).
          stepz F_151e8 D_151e8.
          apply mst_refl.
        + gres. unfold NEGB. apply zv_add_wrap. reflexivity.
        + post.
      - eexists. split; [|split].
        + stepb_ft F_151d0 D_151d0 ltac:(rwR; rewrite zc_ltu by lia; apply Z.ltb_ge; lia).
          stepz F_151d4 D_151d4. stepz F_151d8 D_151d8.
          apply mst_refl.
        + gres. f_equal. lia.
        + post.
    Qed.

    Lemma adlc_D : forall regs (C1 S2v : Z),
      getr regs 1 = retw ->
      getr regs 10 = Z_to_bv 64 65520 -> getr regs 13 = Z_to_bv 64 C1 -> getr regs 11 = Z_to_bv 64 S2v ->
      getr regs 12 = Z_to_bv 64 NEGB ->
      0 <= C1 < two32 -> 0 <= S2v < two32 ->
      exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x15298 : word) m rom) (mkst r retw m rom)
        /\ getr r 10 = Z_to_bv 64
             (Z.lor ((let c2 := if 131041 <? S2v then S2v - 131042 else S2v in
                      if 65520 <? c2 then c2 - 65521 else c2) * 2 ^ 16)
                    (if 65520 <? C1 then C1 - 65521 else C1))
        /\ keeps_cs regs r.
    Proof.
      intros regs C1 S2v R1 R10 R13 R11 R12 HC1 HS2.
      remember (if 65520 <? C1 then C1 - 65521 else C1) as F1 eqn:HF1d.
      remember (if 131041 <? S2v then S2v - 131042 else S2v) as C2 eqn:HC2d.
      cbv zeta.
      remember (if 65520 <? C2 then C2 - 65521 else C2) as F2 eqn:HF2d.
      assert (HC2 : 0 <= C2 < two32) by (rewrite HC2d; destruct (Z.ltb_spec 131041 S2v); lia).
      eexists. split; [|split].
      - stepi F_151ec D_151ec; znorm. zval (if 65520 <? C1 then 1 else 0) ltac:(apply zv_sltu; lia).
        stepz F_151f0 D_151f0. stepz F_151f4 D_151f4. stepz F_151f8 D_151f8.
        stepz F_151fc D_151fc. zval F1 ltac:(rewrite HF1d; apply csel_lemma; reflexivity).
        stepz F_15200 D_15200. stepz F_15204 D_15204. stepz F_15208 D_15208.
        stepi F_1520c D_1520c; znorm. zval (if 131041 <? S2v then 1 else 0) ltac:(apply zv_sltu; lia).
        stepz F_15210 D_15210. stepz F_15214 D_15214. stepz F_15218 D_15218.
        stepz F_1521c D_1521c. zval C2 ltac:(rewrite HC2d; apply csel_lemma; reflexivity).
        stepi F_15220 D_15220; znorm. zval (if 65520 <? C2 then 1 else 0) ltac:(apply zv_sltu; lia).
        stepz F_15224 D_15224. stepz F_15228 D_15228. stepz F_1522c D_1522c. stepz F_15230 D_15230.
        stepz F_15234 D_15234.
        zval (F2 * 2 ^ 16) ltac:(rewrite (csel_lemma _ _ _ (65521 * 2 ^ 16)) by reflexivity;
                                 rewrite HF2d; destruct (65520 <? C2); f_equal; lia).
        stepz F_15238 D_15238.
        stepret F_1523c D_1523c retw ltac:(rwR; reflexivity).
        apply mst_refl.
      - gres. reflexivity.
      - solve_cs.
    Qed.

    Theorem adlc_run : forall regs,
      getr regs 1 = retw ->
      getr regs 10 = Z_to_bv 64 av1 -> getr regs 11 = Z_to_bv 64 av2 -> getr regs 12 = Z_to_bv 64 n ->
      exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x151e4 : word) m rom) (mkst r retw m rom)
        /\ getr r 10 = Z_to_bv 64 (adler32_combine_model av1 av2 n)
        /\ keeps_cs regs r.
    Proof.
      intros regs R1 R10 R11 R12.
      pose proof (lo1_range av1) as Hl1. pose proof (lo2_range av2) as Hl2.
      pose proof (hi1_range av1) as Hh1. pose proof (hi2_range av2) as Hh2.
      pose proof (rem_range n Hn) as Hrem. pose proof (s2m_range av1 n Hn) as Hs2m.
      destruct (adlc_A regs av1 av2 n R10 R11 R12 Ha1 Ha2 Hn) as (r1 & M1 & A12 & A10 & A14 & A15 & A16 & A17 & A5 & A6 & A1 & K1).
      destruct (adlc_B r1 A12 A10 A14 A15 A16 A17 A5 A6) as (r2 & M2 & B10 & B13 & B11 & B12 & B1 & K2).
      destruct (adlc_C r2 (S1 av1 av2) B10 B13 B12 ltac:(unfold S1; lia)) as (r3 & M3 & C13 & C10 & C12 & C11 & C1 & K3).
      rewrite B11 in C11.
      assert (HC1 : 0 <= (if 65520 <? S1 av1 av2 then S1 av1 av2 - 65521 else S1 av1 av2) < two32).
      { unfold S1. destruct (Z.ltb_spec 65520 (lo1 av1 + lo2 av2 + 65535 - 15)); lia. }
      rewrite A1, R1 in B1. rewrite B1 in C1.
      destruct (adlc_D r3 _ (S2 av1 av2 n) C1 C10 C13 C11 C12 HC1 ltac:(unfold S2; lia)) as (r4 & M4 & V4 & K4).
      exists r4. split; [|split].
      - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|].
        eapply msteps_trans; [exact M3 | exact M4].
      - rewrite V4. rewrite <- (adlc_val_model av1 av2 n Ha1 Hn) by lia. reflexivity.
      - eapply keeps_cs_trans; [exact K1|]. eapply keeps_cs_trans; [exact K2|].
        eapply keeps_cs_trans; [exact K3 | exact K4].
    Qed.
  End ARGS.
End ADLC.

Theorem s0_adler32_combine {RCa1 : RunCtx}  : S0_adler32_combine_stmt.
Proof.
  intros regs m rom retw a1 a2 len2 R1 Hret R10 R11 R12 Ha1 Ha2 Hn Himg.
  exact (adlc_run m rom retw Hret Himg a1 a2 len2 Ha1 Ha2 Hn regs R1 R10 R11 R12).
Qed.
