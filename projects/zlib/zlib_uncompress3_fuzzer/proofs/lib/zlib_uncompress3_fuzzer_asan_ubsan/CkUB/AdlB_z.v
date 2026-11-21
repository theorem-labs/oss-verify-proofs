(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.cks Require Import CkTables CkModel CkMathAdler CkWalk.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CkU Require Import AdlAGlue.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CkUB Require Import CkBImg CkBTables CkBShadow CkBIface CkBKit AdlB_zs AdlB_zt AdlB_zn.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shrng.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (adler A n : Z) (bs : list Z).
  Hypothesis LOS : lo <= bv_unsigned sp - 176.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis AR : 0 <= adler < 2^64.
  Hypothesis A1R : 1 <= A.
  Hypothesis NL : Z.of_nat (length bs) = n.
  Hypothesis ALO : A + n <= lo.
  Hypothesis BF : Forall (fun b => 0 <= b < 256) bs.
  Hypothesis UNP : unpoisoned m A (A + n).
  Hypothesis RB : rng RNG A n.
  Hypothesis RS : shrng RNG A (A + n).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - 176, SP)].
  Notation POST res := (ck_postA 176 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc res lo m).
  Notation CTX L := (L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo adler A n bs
                       LOS KLO AR A1R NL ALO BF UNP RB RS RI RSTK).

  Lemma adl_entry : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv asegs m -> stk asegs m lo SP -> rt_got m -> rt_shbase m -> bytes_at asegs m A (zb bs) ->
    evtF asegs RNG (POST (adler32_z_model adler bs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 adler) (Z_to_bv 64 A) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0x962b0) fc None m (seg_rom asegs)).
  Proof using All.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MI ST GOT SHB BY.
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (zb_length bs) as ZBL.
    pose proof (lo16_range adler) as LR. pose proof (hi16_range adler) as HR.
    assert (N0 : 0 <= n) by lia.
    carve_frame 176%nat ST.
    do 14 zstep.
    do 8 zstep.
    rewrite lo16_mach, (hi16_mach adler ltac:(lia)).
    replace (SP + -176) with (SP - 176) in MU by lia.
    zstep.
    if_cases K1; zify_cond K1.
    2:{
        eapply (CTX adl_len1); [exact K1|].
        split; [eexists; exact FR0|]. repeat (split; [assumption|]). assumption. }
    do 1 zstep. if_cases KA; zify_cond KA. { exfalso. lia. }
    do 2 zstep. if_cases K16; zify_cond K16.
    -
      do 5 zstep.
      assert (MB : adler32_z_model adler bs = adl_blocks_res (Z.to_nat (n / 5552)) (lo16 adler, hi16 adler) (skipn (Z.to_nat 0) bs)).
      { change (skipn (Z.to_nat 0) bs) with bs. rewrite <- NL. apply adl_model_blocks. unfold Zlen. lia. }
      if_cases KN; zify_cond KN; rewrite Z.shiftr_div_pow2 in KN by lia; change (2 ^ 4) with 16 in KN.
      +
        do 2 zstep.
        replace (n / 5552) with 0 in MB by (Z.div_mod_to_equations; lia). change (Z.to_nat 0) with 0%nat in MB at 1.
        rewrite (adl_blocks_res_0_cons _ _ (skipn_nonnil n bs NL 0 ltac:(lia))) in MB.
        replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) by (f_equal; lia).
        replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
        eapply (CTX adl_tail_setup); [ | | | | |exact MB| ]; try lia.
        split; [eexists; eexists; exact FR0|]. repeat (split; [assumption|]). assumption.
      +
        do 15 zstep.
        pose proof (CTX adl_outer (Z.to_nat (n / 5552)) 0) as HO. rewrite Z.add_0_r, Z.sub_0_r in HO.
        eapply HO; [ | | | | |exact MB| ]; try lia.
        split; [eexists; eexists; exact FR0|]. repeat (split; [assumption|]). assumption.
    -
      assert (SE : adler32_z_model adler bs =
                   Z.lor ((snd (adler_fold (lo16 adler, hi16 adler) (skipn (Z.to_nat 0) bs)) mod BASE) * 65536)
                         (csub (fst (adler_fold (lo16 adler, hi16 adler) (skipn (Z.to_nat 0) bs))))).
      { change (skipn (Z.to_nat 0) bs) with bs. rewrite <- (adler_short_exit adler bs); [reflexivity| unfold Zlen; lia | unfold Zlen; lia]. }
      zstep. if_cases KZ; zify_cond KZ.
      +
        assert (BN : bs = []) by (destruct bs; [reflexivity| cbn in NL; lia]).
        assert (SE0 : adler32_z_model adler bs = Z.lor (hi16 adler mod BASE * 65536) (csub (lo16 adler))).
        { rewrite SE. change (skipn (Z.to_nat 0) bs) with bs. rewrite BN. reflexivity. }
        eapply (CTX adl_short_fin); [ | |exact SE0| ]; try lia.
        split; [eexists; exact FR0|]. repeat (split; [assumption|]). assumption.
      + do 2 zstep.
        replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) by (f_equal; lia).
        replace (Z_to_bv 64 n) with (Z_to_bv 64 (n - 0)) by (f_equal; lia).
        eapply (CTX adl_short_loop (Z.to_nat n) 0); [ | | | | | |exact SE| ]; try lia.
        split; [eexists; exact FR0|]. repeat (split; [assumption|]). assumption.
  Qed.
End P.

Theorem adler32_z_proofA : adler32_z_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         FR fc m lo adler A bs MI ST LOS KLO GOT SHB A0 AR A1 A1R ALO A2 (BY & BF & UNP & RB & RS) RI RSTK.
  subst a0 a1 a2. unfold CK_ADLER32Z_STACK in *. unfold ACK_ADLER32Z.
  eapply (adl_entry RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo adler A (Z.of_nat (length bs)) bs
                    LOS KLO AR A1R eq_refl ALO BF UNP RB RS RI RSTK); assumption.
Qed.

Theorem adler32_z_null_proofA : adler32_z_null_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         FR fc m lo MI ST LOS KLO GOT SHB A1 A2 RI RSTK.
  subst a1 a2. unfold CK_ADLER32Z_STACK in *. unfold ACK_ADLER32Z.
  pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 176%nat ST.
  do 14 zstep. do 8 zstep.
  replace (bv_unsigned sp + -176) with (bv_unsigned sp - 176) in MU by lia.
  zstep. if_true. zstep. if_true.
  assert (UNP0 : unpoisoned m lo (lo + 0)) by (replace (lo + 0) with lo by lia; apply unpoisoned_nil; lia).
  assert (RB0 : rng RNG lo 0) by (eapply rng_sub'; [exact RSTK| lia]).
  assert (RS0 : shrng RNG lo (lo + 0)) by (intros H; lia).
  eapply (adl_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo 0 lo 0 []
                  LOS KLO ltac:(lia) ltac:(lia) eq_refl ltac:(lia) (Forall_nil _) UNP0 RB0 RS0 RI RSTK 1).
  split; [eexists; exact FR0|]. repeat (split; [assumption|]).
  apply bytes_at_nil. lia.
Qed.
