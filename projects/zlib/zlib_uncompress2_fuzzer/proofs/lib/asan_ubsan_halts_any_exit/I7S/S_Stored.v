(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require Import SBase S_StoredA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Section WITH_MEMCPY.
Hypothesis MEMCPY : memcpy_spec_s.

Lemma stored_loop : forall (k : nat) cx fin MD T Rb l M (cin0' cinj holdj j : Z),
  let cx' := cx in
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_S cx ->
  j = 32 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS8 = j -> zget_l Rb l kA3 = j ->
  zget_l Rb l kA4 = c_q cx + cinj -> zget_l Rb l kS11 = c_q cx + cinj ->
  zget_l Rb l kS2 = c_n cx - cinj -> zget_l Rb l kS7 = holdj ->
  mem_arr 1 R_segs M (c_q cx) (c_n cx) fin ->
  (forall R' hold',
     zget R' kA4 = c_q cx + c_n cx -> zget R' kS2 = 0 -> zget R' kS7 = hold' ->
     zget R' kS8 = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ (j + 8 * (c_n cx - cinj)) -> c_n cx - cinj < Z.of_nat k ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS3 = zget_l Rb l kS3 ->
     zget R' kS4 = zget_l Rb l kS4 -> 
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kT4 = zget_l Rb l kT4 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kT6 = zget_l Rb l kT6 ->
     realizes R_segs (zcfg R_segs L_LEAVE_A4 (zupd R' []) M MD) T) ->
  (forall R' hold',
     zget R' kS11 = c_q cx + cinj + Z.of_nat k -> zget R' kS2 = c_n cx - cinj - Z.of_nat k -> zget R' kS7 = hold' ->
     zget R' kS8 = 32 -> 0 <= hold' < 2 ^ 32 -> Z.of_nat k <= c_n cx - cinj ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kS3 = zget_l Rb l kS3 ->
     zget R' kS4 = zget_l Rb l kS4 -> 
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kT4 = zget_l Rb l kT4 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kT6 = zget_l Rb l kT6 ->
     realizes R_segs (zcfg R_segs L_STORED_BODY (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_STORED_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M cin0' cinj holdj j cx' Hh Hfin CXl Hj Hk Hc Hhj Hjc L9 L0 LA3 LA4 L10 L8 L7 Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. subst cx'.
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
  zkeysb. unfold L_STORED_LOOP, L_STORED_BODY, L_LEAVE_A4 in *. pose proof two64_eq as TW64.
  assert (Hj32 : 2 ^ j <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 32) with 4294967296 in Hj32.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  -
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj) end; try zreg; try lia.
    + replace (j + 8 * (n - cinj)) with j by lia. lia.
  - zbr Rfd true.
    pose proof (Hfin cinj ltac:(lia)) as Hb0.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (fin cinj * 2 ^ j) ltac:(rewrite (Z.mod_small j) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    destruct k as [|k'].
    +
      zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj)) end; try zreg; try lia.
      replace 32 with (j + 8) by lia. lia.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' M cin0' (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) Hh Hfin) end;
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S]; split_conj; assumption || lia
        | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | (icx_cbn; zreg) .. | exact Hin | | ].
      * intros R' hold'. icx_cbn. intros. eapply KLV; try eassumption; try lia; try zkept.
        all: replace (j + 8 * (n - cinj)) with (j + 8 + 8 * (n - (cinj + 1))) by lia; assumption.
      * intros R' hold'. icx_cbn. intros. eapply KDN; try eassumption; try lia; try zkept.
        all: assumption.
Qed.

Theorem arm_STORED_s : arm_stmt L_STORED STORED.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0. pose proof K as KA0.
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_. pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  assert (Hk : 0 <= bits mod 8 <= bits) by (Z.to_euclidean_division_equations; lia).
  pose proof (shiftr_lt_pow2 hold bits (bits mod 8) ltac:(lia) ltac:(lia)) as Hsh.
  zkeysb. unfold L_STORED, L_STORED_LOOP, L_STORED_BODY, L_STORED_BAD, L_LEAVE_A4, L_LEAVE, L_LEAVE_LD, L_BADMSG_S10, L_COPY_ in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  zsetreg (bits mod 8) ltac:(symmetry; apply land7_mod; lia).
  zstep Rfd.
  zstep Rfd.
  zsetreg (Z.shiftr hold (bits mod 8))
    ltac:(rewrite (Z.mod_small hold) by lia; rewrite (Z.mod_small (bits mod 8)) by (Z.to_euclidean_division_equations; lia); reflexivity).
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (BODY : forall RJ cin1 hold1 bits1,
    zget RJ kSP = u + -224 -> zget RJ kGP = K0 kGP -> zget RJ kTP = K0 kTP -> zget RJ kS0 = p ->
    zget RJ kA0 = u -> zget RJ kA1 = 0 -> zget RJ kS6 = p + 168 -> zget RJ kT6 = -16180 ->
    zget RJ kT4 = 30 -> zget RJ kS9 = 67008 -> zget RJ kS4 = 16209 ->
    zget RJ kS2 = n - cin1 -> zget RJ kS3 = ob + cout -> zget RJ kRA = osz - cout ->
    zget RJ kS11 = q + cin1 -> zget RJ kS7 = hold1 -> zget RJ kS8 = bits1 ->
    cin <= cin1 <= n -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (n - cin1) + bits1 = 8 * (n - cin) + (bits - bits mod 8) ->
    realizes R_segs (zcfg R_segs 87996 (zupd RJ []) Mc MD) T) end.
  { intros RJ cin1 hold1 bits1. intros. zkeys.
    pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh1.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (hold1 mod 65536) ltac:(symmetry; apply low16_of_shift; lia).
    zstep Rfd.
    zsetreg (Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536)) ltac:(rewrite (Z.mod_small hold1 18446744073709551616) by lia; reflexivity).
    assert (Hx : 0 <= Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536) < 18446744073709551616).
    { change 18446744073709551616 with (2 ^ 64). apply lxor_bound.
      - pose proof (shiftr_lt_pow2 hold1 bits1 16 ltac:(lia) ltac:(assumption)) as X.
        assert (2 ^ (bits1 - 16) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
      - Z.to_euclidean_division_equations; lia. }
    assert (Hm16 : 0 <= hold1 mod 65536 < 65536) by (Z.to_euclidean_division_equations; lia).
    destruct (Z.eq_dec (Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536)) 65535) as [EQ | NE].
    -
      rewrite EQ.
      zstep Rfd. zlit.
      zbr Rfd false.
      zstep Rfd.
      unfold st_rest in SREST. icx_cbn.
      dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      tstep1 Rfd.
      zstep Rfd.
      zbr Rfd true.
      pose proof (sinv_set _ _ lf cf COPY_ cin1 cout 0 0 (hold1 mod 65536) SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(intros _; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    COPY_ cin1 cout 0 0 (hold1 mod 65536) ltac:(left; unfold Wm; cbn; lia)) as MB1.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
        eapply (arm_COPY__s MEMCPY (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                  (set_st (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY_ cin1 cout 0 0 (hold1 mod 65536))
                  lf cf CX0 Hh Hfin eq_refl SI1) end.
      + unfold s_regs_arm, s_fix, s_vars, set_st; icx_cbn; zkeys; split_conj; zreg.
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std | unfold st_at, st_rest; icx_cbn; split_conj; assumption | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HAG ].
      + eapply KALL_mono; [| exact KA0]. lia.
    -
      zstep Rfd. zlit.
      assert (Hne : Z.lxor (Z.shiftr hold1 16) (hold1 mod 65536) mod 18446744073709551616 <> 65535) by (rewrite Z.mod_small by lia; exact NE).
      zbr Rfd true.
      zstep Rfd. zstep Rfd. zlit.
      zstep Rfd.
      pose proof (sinv_set _ _ lf cf BAD cin1 cout hold1 bits1 length SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(cbv [COPY_ COPY BAD]; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      pose proof (meas_set (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    BAD cin1 cout hold1 bits1 length ltac:(right; split; [unfold Wm; cbn; lia | vm_compute; reflexivity])) as MB1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        eapply (KB10 R' Mx (set_st (IST STORED last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                               STORED cin1 cout hold1 bits1 length) lf cf) end.
      + unfold bad_of, set_st; cbn. exact SI1.
      + unfold bad_of, set_st; cbn. unfold set_st in MB1; cbn in MB1. exact MB1.
      + unfold s_regs_d10, s_fix, s_vars, set_st; icx_cbn; zkeys; split_conj; zreg.
      + zreg.
      + unfold k_mem, set_st; icx_cbn; split_conj;
          [ close_std | split; [exact Hmode | exact SREST] | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HAG ]. }
  destruct (Z_lt_dec 31 bits) as [Hb32 | Hb32].
  -
    zbr Rfd true.
    zstep Rfd.
    zsetreg (bits - bits mod 8) ltac:(symmetry; apply landm8; lia).
    assert (Hmono : 2 ^ (bits - bits mod 8) <= 2 ^ bits) by (apply Z.pow_le_mono_r; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (BODY R' cin (Z.shiftr hold (bits mod 8)) (bits - bits mod 8)) end;
      first [zreg | lia | Z.to_euclidean_division_equations; lia].
  -
    zbr Rfd false.
    zstep Rfd.
    zsetreg (bits - bits mod 8) ltac:(symmetry; apply land24; lia).
    zstep Rfd.
    zstep Rfd.
    assert (Hkk : exists k : nat, bits - bits mod 8 = 32 - 8 * Z.of_nat k /\ (1 <= k <= 4)%nat).
    { exists (Z.to_nat (4 - bits / 8)). rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (stored_loop k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx cin0 cin (Z.shiftr hold (bits mod 8)) (bits - bits mod 8) Hh Hfin CXl Hk1 Hk2) end;
      [ icx_cbn; lia | exact Hsh | lia | zreg .. | exact Hin | | ].
    +
      intros R' hold'. icx_cbn. intros. zimps. zkeys. unfold L_LEAVE_A4, L_LEAVE_LD in *.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_set _ _ lf cf STORED n cout hold' (bits - bits mod 8 + 8 * (n - cin)) length SI0 Hfl eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(cbv [COPY_ COPY STORED]; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(cbn; unfold Wm; cbn; lia)) as SI1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx _ lf cf SI1) end.
      * unfold s_regs_leave_ld, set_st; icx_cbn; zkeys; split_conj; try zreg. all: zkept.
      * close_std.
      * unfold set_st; split; [exact Hmode | exact SREST].
      * exact SRET.
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' hold'. icx_cbn. intros. zimps. zkeys. unfold L_STORED_BODY in *.
      apply (BODY R' (cin + Z.of_nat k) hold' 32); try zkept; try lia.
Qed.

End WITH_MEMCPY.
End FXG.
