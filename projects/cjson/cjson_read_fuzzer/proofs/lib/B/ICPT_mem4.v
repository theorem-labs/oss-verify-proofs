(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow ICPT_iface RT_poison RT_poison2 F_memcpy ICPT_mem ICPT_mem2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MemcpyIcpt.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (d s n lo : Z) (src junk : list byte).
  Hypothesis HN : 0 <= n < 2^40.
  Hypothesis LEN : Z.of_nat (length src) = n.
  Hypothesis ARS : app_range s n.
  Hypothesis ARD : app_range d n.
  Hypothesis WR : wr_range_ok d n.
  Hypothesis OV : s + n <= d \/ d + n <= s.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + AINTRIN_STACK <= bv_unsigned sp.
  Hypothesis SEPS : s + n <= lo \/ bv_unsigned sp <= s.
  Hypothesis SEPD : d + n <= lo \/ bv_unsigned sp <= d.

  Lemma RBs : 0 <= s /\ s + n < 2^47. Proof. exact (app_range_lt47 s n ARS). Qed.
  Lemma RBd : 0 <= d /\ d + n < 2^47. Proof. exact (app_range_lt47 d n ARD). Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv : AINTRIN_STACK = 2304. Proof. reflexivity. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (memcpy_like_post AINTRIN_STACK rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9 s10 s11 F fc d s n src lo m).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9
            (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition imc_frame (mm : word -> option byte) : Prop :=
    mem_inv bsegs mm /\ icpt_cells mm /\ stk bsegs mm lo (bv_unsigned sp + -2160)
    /\ rw_cells bsegs mm (bv_unsigned sp + -80) [C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ rw_cells bsegs mm d [CB (Z.to_nat n) junk]
    /\ bytes_at bsegs mm s src
    /\ munch [(d, d + n); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)] m mm /\ wmono bsegs m mm
    /\ stk bsegs mm (bv_unsigned sp + -2160) (bv_unsigned sp + -80)
    /\ (0 < n -> shadow_ok mm s n) /\ (0 < n -> shadow_ok mm d n).

  Ltac imc_intro AF := (nelim AF 11%nat; intros MI' IC' ST' FR' DST' SRC' MU' WM' ST2 SOS SOD).
  Ltac imc_pack := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); assumption.

  (* [comment removed for export] *)
  Lemma imc_after_region : forall mm mm',
    icpt_cells mm -> (0 < n -> shadow_ok mm s n) -> (0 < n -> shadow_ok mm d n) ->
    munch [(bv_unsigned sp - 2240, bv_unsigned sp - 2160)] mm mm' ->
    icpt_cells mm' /\ (0 < n -> shadow_ok mm' s n) /\ (0 < n -> shadow_ok mm' d n).
  Proof.
    intros mm mm' IC SOS SOD MUr. pose proof RBs. pose proof RBd. pose proof CEILv. pose proof STKv.
    split; [| split].
    - eapply icpt_cells_munch; [exact IC| exact MUr|]. unfold icpt_cell_ivs.
      repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - intros N0. pose proof (SH_bounds s ltac:(lia)). pose proof (SH_bounds (s + n - 1) ltac:(lia)).
      eapply shadow_ok_munch; [exact (SOS N0)| exact MUr| exact N0| lia| lia|]. cbn. lia.
    - intros N0. pose proof (SH_bounds d ltac:(lia)). pose proof (SH_bounds (d + n - 1) ltac:(lia)).
      eapply shadow_ok_munch; [exact (SOD N0)| exact MUr| exact N0| lia| lia|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma imc_call : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    imc_frame mm ->
    evt bsegs POST (ST_ 0x53c2c mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. imc_intro AF.
    pose proof RBs as RS. pose proof RBd as RD. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    icpt_split IC'.
    zstep. zstep. zstep.
    call memcpy_callv; [exact SRC'| lia| exact DST'| exact OV| lia| lia| lia| exact MI'|].
    do 13 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with ST1 : stk bsegs mm2 lo _ |- _ =>
      lazymatch goal with ST3 : stk bsegs mm2 (bv_unsigned sp + -2160) _ |- _ =>
      lazymatch goal with FR3 : rw_cells bsegs mm2 (bv_unsigned sp + -80) _ |- _ =>
        pose proof (stk_merge bsegs mm2 _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end end end.
    finish.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma imc_wregion : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    imc_frame mm -> 0 < n ->
    evt bsegs POST (ST_ 0x53fd0 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF N0. imc_intro AF.
    pose proof RBs as RS. pose proof RBd as RD. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof IC' as IC2. pose proof SOS as SOS2. pose proof SOD as SOD2.
    pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp - 2160)] mm) as MU1.
    do 5 zstep.
    callsp region_is_poisoned_ok;
      [ exact IC' | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact ARD | apply SOD; exact N0 | ].
    do 5 zstep. fold_lits. sh_if_true.
    apply imc_call.
    lazymatch goal with |- imc_frame ?mm2 =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
        (nelim (imc_after_region mm mm2 IC2 SOS2 SOD2 MUc) 3%nat; intros IC3 SOS3 SOD3)
      end end.
    imc_pack.
  Qed.

  (* [comment removed for export] *)
  Lemma imc_w378 : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    imc_frame mm ->
    evt bsegs POST (ST_ 0x53d48 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBd as RD.
    zstep. if_cases K; zify_cond K.
    - apply imc_wregion; [exact AF| lia].
    - zstep. apply imc_call. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma imc_w59c : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    imc_frame mm -> 0 < n ->
    evt bsegs POST (ST_ 0x53fc8 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF N0. pose proof RBd as RD.
    zstep. zstep. if_cases K.
    - apply imc_call. exact AF.
    - apply imc_wregion; [exact AF| exact N0].
  Qed.

  (* [comment removed for export] *)
  Lemma imc_wloop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 x9 (acc : word) x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    imc_frame mm -> 0 < n ->
    Z.to_nat (SH (d + n - 1) - SH d - i) = k -> 0 <= i -> SH d + i < SH (d + n - 1) ->
    evt bsegs POST (ST_ 0x53fb8 mm x1 x5 x6 x7 x9 (Z_to_bv 64 (2147450880 + d / 8 + i)) (Z_to_bv 64 (2147450880 + (d + n - 1) / 8)) acc x16 x17
                        x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 x9 acc x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 AF N0 Hk Hi Hlt;
      pose proof RBd as RB; pose proof (SH_bounds d ltac:(lia)) as B1; pose proof (SH_bounds (d + n - 1) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    pose proof AF as AF'. imc_intro AF'.
    assert (V : exists b, mm (wa (2147450880 + d / 8 + i)) = Some b).
    { destruct (mm (wa (2147450880 + d / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 (SOD N0) (2147450880 + d / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - replace (2147450880 + d / 8 + i + 1) with (2147450880 + d / 8 + (i + 1)) by lia.
      apply (IH (i + 1)); try assumption; lia.
    - replace (2147450880 + d / 8 + i + 1) with (2147450880 + (d + n - 1) / 8) by lia.
      apply imc_w59c; [exact AF| exact N0].
  Qed.

  (* [comment removed for export] *)
  Lemma imc_wslow : forall mm x1 x5 x6 x7 x9 x15 x16 x17 x18 x19 x21 x22 x23 x24 x28 x29 x30 x31,
    imc_frame mm -> 0 < n ->
    evt bsegs POST (ST_ 0x53f9c mm x1 x5 x6 x7 x9 (Z_to_bv 64 (2147450880 + d / 8)) (Z_to_bv 64 (2147450880 + (d + n - 1) / 8))
                        x15 x16 x17 x18 x19 (Z_to_bv 64 (d + n - 1)) x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF N0. pose proof RBd as RB.
    pose proof (SH_bounds d ltac:(lia)) as B1. pose proof (SH_bounds (d + n - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. imc_intro AF'.
    (nelim (shadow_ok_shb mm d n (n - 1) (SOD N0) ltac:(lia)) 3%nat; intros ve SHE Ce).
    replace (d + (n - 1)) with (d + n - 1) in SHE, Ce by lia.
    pose proof (shb_load_div' mm (d + n - 1) ve (d + n - 1) SHE eq_refl ltac:(lia)) as RD.
    step. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases K; zify_cond K.
    - apply imc_w59c; [exact AF| exact N0].
    - replace (2147450880 + d / 8) with (2147450880 + d / 8 + 0) by lia.
      eapply (imc_wloop mm (Z.to_nat (SH (d + n - 1) - SH d - 0)) 0); try exact AF; unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma imc_wquick : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x28 x29 x30 x31,
    imc_frame mm -> 0 < n <= 64 ->
    evt bsegs POST (ST_ 0x53bf4 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (d + n)) x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF N64. pose proof RBd as RB.
    pose proof (SH_bounds d ltac:(lia)) as B1. pose proof (SH_bounds (d + n - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. imc_intro AF'.
    icpt_split IC'.
    do 8 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    replace (d + n + -1) with (d + n - 1) by lia.
    zstep. zstep. rewrite !land_m8 by lia.
    destruct (vis_read8 mm ((2147450880 + d / 8) / 8 * 8)) as (w1 & L1 & W1). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 (SOD ltac:(lia))). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 mm ((2147450880 + (d + n - 1) / 8) / 8 * 8)) as (w2 & L2 & W2). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 (SOD ltac:(lia))). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases K.
    - apply imc_wslow; [exact AF| lia].
    - apply imc_call. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma imc_w21c : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x28 x29 x30 x31,
    imc_frame mm ->
    evt bsegs POST (ST_ 0x53be4 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (d + n)) x21 (Z_to_bv 64 (n + -65)) x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBd as RB.
    zstep. zstep. fold_lits. rewrite (zb_lxor_ones d) by lia. sh_if_false.
    zstep. zstep. fold_lits.
    destruct (Z.eq_dec n 0) as [N0|N0].
    { sh_if_true. apply imc_w378. exact AF. }
    destruct (Z.lt_ge_cases 64 n) as [N64|N64].
    { sh_if_true. apply imc_w378. exact AF. }
    sh_if_false. apply imc_wquick; [exact AF| lia].
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma imc_rregion : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x28 x29 x30 x31,
    imc_frame mm -> 0 < n ->
    evt bsegs POST (ST_ 0x53ed0 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (d + n)) x21 (Z_to_bv 64 (n + -65)) x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF N0. imc_intro AF.
    pose proof RBs as RS. pose proof RBd as RD. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof IC' as IC2. pose proof SOS as SOS2. pose proof SOD as SOD2.
    pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp - 2160)] mm) as MU1.
    do 6 zstep.
    callsp region_is_poisoned_ok;
      [ exact IC' | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact ARS | apply SOS; exact N0 | ].
    do 5 zstep. fold_lits. sh_if_true.
    apply imc_w21c.
    lazymatch goal with |- imc_frame ?mm2 =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
        (nelim (imc_after_region mm mm2 IC2 SOS2 SOD2 MUc) 3%nat; intros IC3 SOS3 SOD3)
      end end.
    imc_pack.
  Qed.

  (* [comment removed for export] *)
  Lemma imc_r4c4 : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x28 x29 x30 x31,
    imc_frame mm ->
    evt bsegs POST (ST_ 0x53e94 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (d + n)) x21 (Z_to_bv 64 (n + -65)) x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBs as RS.
    zstep. if_cases K; zify_cond K.
    - apply imc_rregion; [exact AF| lia].
    - zstep. apply imc_w21c. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma imc_r4f8 : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x28 x29 x30 x31,
    imc_frame mm -> 0 < n ->
    evt bsegs POST (ST_ 0x53ec8 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (d + n)) x21 (Z_to_bv 64 (n + -65)) x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF N0. pose proof RBs as RS.
    zstep. zstep. if_cases K.
    - apply imc_w21c. exact AF.
    - apply imc_rregion; [exact AF| exact N0].
  Qed.

  (* [comment removed for export] *)
  Lemma imc_rloop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 x9 (acc : word) x16 x17 x18 x19 x21 x23 x24 x28 x29 x30 x31,
    imc_frame mm -> 0 < n ->
    Z.to_nat (SH (s + n - 1) - SH s - i) = k -> 0 <= i -> SH s + i < SH (s + n - 1) ->
    evt bsegs POST (ST_ 0x53eb8 mm x1 x5 x6 x7 x9 (Z_to_bv 64 (2147450880 + s / 8 + i)) (Z_to_bv 64 (2147450880 + (s + n - 1) / 8)) acc x16 x17
                        x18 x19 (Z_to_bv 64 (d + n)) x21 (Z_to_bv 64 (n + -65)) x23 x24 x28 x29 x30 x31).
  Proof.
    intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 x9 acc x16 x17 x18 x19 x21 x23 x24 x28 x29 x30 x31 AF N0 Hk Hi Hlt;
      pose proof RBs as RB; pose proof (SH_bounds s ltac:(lia)) as B1; pose proof (SH_bounds (s + n - 1) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    pose proof AF as AF'. imc_intro AF'.
    assert (V : exists b, mm (wa (2147450880 + s / 8 + i)) = Some b).
    { destruct (mm (wa (2147450880 + s / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 (SOS N0) (2147450880 + s / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - replace (2147450880 + s / 8 + i + 1) with (2147450880 + s / 8 + (i + 1)) by lia.
      apply (IH (i + 1)); try assumption; lia.
    - replace (2147450880 + s / 8 + i + 1) with (2147450880 + (s + n - 1) / 8) by lia.
      apply imc_r4f8; [exact AF| exact N0].
  Qed.

  (* [comment removed for export] *)
  Lemma imc_rslow : forall mm x1 x5 x6 x7 x9 x15 x16 x17 x18 x21 x23 x24 x28 x29 x30 x31,
    imc_frame mm -> 0 < n ->
    evt bsegs POST (ST_ 0x53e9c mm x1 x5 x6 x7 x9 (Z_to_bv 64 (2147450880 + s / 8)) (Z_to_bv 64 (2147450880 + (s + n - 1) / 8))
                        x15 x16 x17 x18 (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (d + n)) x21 (Z_to_bv 64 (n + -65)) x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF N0. pose proof RBs as RB.
    pose proof (SH_bounds s ltac:(lia)) as B1. pose proof (SH_bounds (s + n - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. imc_intro AF'.
    (nelim (shadow_ok_shb mm s n (n - 1) (SOS N0) ltac:(lia)) 3%nat; intros ve SHE Ce).
    replace (s + (n - 1)) with (s + n - 1) in SHE, Ce by lia.
    pose proof (shb_load_div' mm (s + n - 1) ve (s + n - 1) SHE eq_refl ltac:(lia)) as RD.
    step. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases K; zify_cond K.
    - apply imc_r4f8; [exact AF| exact N0].
    - replace (2147450880 + s / 8) with (2147450880 + s / 8 + 0) by lia.
      eapply (imc_rloop mm (Z.to_nat (SH (s + n - 1) - SH s - 0)) 0); try exact AF; unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma imc_rquick : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x24 x28 x29 x30 x31,
    imc_frame mm -> 0 < n <= 64 ->
    evt bsegs POST (ST_ 0x53bac mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (s + n)) (Z_to_bv 64 (d + n)) x21 (Z_to_bv 64 (n + -65)) x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF N64. pose proof RBs as RB.
    pose proof (SH_bounds s ltac:(lia)) as B1. pose proof (SH_bounds (s + n - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. imc_intro AF'.
    icpt_split IC'.
    do 8 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    replace (s + n + -1) with (s + n - 1) by lia.
    zstep. zstep. rewrite !land_m8 by lia.
    destruct (vis_read8 mm ((2147450880 + s / 8) / 8 * 8)) as (w1 & L1 & W1). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 (SOS ltac:(lia))). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 mm ((2147450880 + (s + n - 1) / 8) / 8 * 8)) as (w2 & L2 & W2). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 (SOS ltac:(lia))). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases K.
    - apply imc_rslow; [exact AF| lia].
    - apply imc_w21c. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma imc_1d0 : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x28 x29 x30 x31,
    imc_frame mm ->
    evt bsegs POST (ST_ 0x53b98 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (s + n)) (Z_to_bv 64 (d + n)) x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBs as RS. pose proof RBd as RD.
    zstep. zstep. fold_lits. rewrite (zb_lxor_ones s) by lia. sh_if_false.
    do 3 zstep. fold_lits.
    destruct (Z.eq_dec n 0) as [N0|N0].
    { sh_if_true. apply imc_r4c4. exact AF. }
    destruct (Z.lt_ge_cases 64 n) as [N64|N64].
    { sh_if_true. apply imc_r4c4. exact AF. }
    sh_if_false. apply imc_rquick; [exact AF| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma imc_body : forall mm x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31,
    imc_frame mm ->
    evt bsegs POST (ST_ 0x53b6c mm rae x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBs as RS. pose proof RBd as RD. pose proof STKv as SE.
    pose proof AF as AF'. imc_intro AF'. icpt_split IC'.
    do 4 zstep. fold_lits. sh_if_false.
    do 4 zstep.
    replace (n + s) with (s + n) by lia. replace (n + d) with (d + n) by lia.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    - apply imc_1d0. exact AF.
    - zstep. if_cases K2; zify_cond K2.
      + apply imc_1d0. exact AF.
      + zstep. sh_if_false. apply imc_1d0. exact AF.
  Qed.
End MemcpyIcpt.

Lemma memcpy_icpt_ok : memcpy_icpt_spec.
Proof.
  unfold memcpy_icpt_spec, memcpy_contract.
  intros until lo. intros IC MI ST CEIL SPB -> -> -> SRC LEN DST OV HN ARS ARD WR SOS SOD SEPS SEPD.
  pose proof (app_range_lt47 s n ARS) as RS. pose proof (app_range_lt47 d n ARD) as RD. pose proof (bv_unsigned_in_range 64 sp) as RSP.
  assert (SE : AINTRIN_STACK = 2304) by reflexivity.
  pose proof (munch_refl [(d, d + n); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (conj IC (conj SOS SOD)) as PK.
  unfold AMEMCPY_T.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 13 zstep.
  (nelim PK 3%nat; intros IC0 SOS0 SOD0). clear IC SOS SOD.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
  assert (IC1 : icpt_cells m0);
  [ eapply icpt_cells_munch_wr; [exact IC0| exact MU| exact WR|]; lia |];
  assert (SOS1 : 0 < n -> shadow_ok m0 s n);
  [ intros N0; pose proof (SH_bounds s ltac:(lia)) as B1; pose proof (SH_bounds (s + n - 1) ltac:(lia)) as B2;
    eapply shadow_ok_munch; [exact (SOS0 N0)| exact MU| exact N0| lia| lia|];
    cbn; unfold SH, SHADOW_OFFSET in *;
    destruct ARD as [AR'|AR']; unfold lowmem_range, highmem_range, KHIGHMEM_BEG, KHIGHMEM_END, KLOWSHADOW_BEG in AR';
      Z.div_mod_to_equations; lia |];
  assert (SOD1 : 0 < n -> shadow_ok m0 d n);
  [ intros N0; pose proof (SH_bounds d ltac:(lia)) as B1; pose proof (SH_bounds (d + n - 1) ltac:(lia)) as B2;
    eapply shadow_ok_munch; [exact (SOD0 N0)| exact MU| exact N0| lia| lia|];
    cbn; unfold SH, SHADOW_OFFSET in *;
    destruct ARD as [AR'|AR']; unfold lowmem_range, highmem_range, KHIGHMEM_BEG, KHIGHMEM_END, KLOWSHADOW_BEG in AR';
      Z.div_mod_to_equations; lia |];
  destruct (stk_split bsegs m0 lo (bv_unsigned sp + -2160) (bv_unsigned sp + -80) ST ltac:(lia)) as [ST1 ST2]
  end.
  eapply imc_body; try eassumption; try lia.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); eassumption.
Qed.



End CeilWrap.
