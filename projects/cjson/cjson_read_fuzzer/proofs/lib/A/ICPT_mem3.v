(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow ICPT_iface RT_poison RT_poison2 F_memset ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MemsetIcpt.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (d c n lo : Z) (junk : list byte).
  Hypothesis HN : 0 <= n < 2^40.
  Hypothesis HC : 0 <= c < 2^64.
  Hypothesis AR : app_range d n.
  Hypothesis WR : wr_range_ok d n.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + AINTRIN_STACK <= bv_unsigned sp.
  Hypothesis SEP : d + n <= lo \/ bv_unsigned sp <= d.
  Hypothesis SO : 0 < n -> shadow_ok m1 d n.

  Lemma R47 : 0 <= d /\ d + n < 2^47.
  Proof. exact (app_range_lt47 d n AR). Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv : AINTRIN_STACK = 2304. Proof. reflexivity. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (memset_like_post AINTRIN_STACK rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 F fc d c n lo m).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
            (Z_to_bv 64 d) (Z_to_bv 64 c) (Z_to_bv 64 n) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ims_frame (mm : word -> option byte) : Prop :=
    mem_inv asegs mm /\ icpt_cells mm /\ stk asegs mm lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs mm (bv_unsigned sp + -64) [C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ rw_cells asegs mm d [CB (Z.to_nat n) junk]
    /\ munch [(d, d + n); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)] m mm /\ wmono asegs m mm
    /\ stk asegs mm (bv_unsigned sp + -2144) (bv_unsigned sp + -64).
  Hypothesis AF1 : ims_frame m1.

  (* [comment removed for export] *)
  Lemma ims_call : forall mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ims_frame mm ->
    evt asegs POST (ST_ 0x538b0 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros nelH_; (nelim nelH_ 8%nat; intros MI' IC' ST' FR' DST' MU' WM' ST2).
    pose proof R47 as RB. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    icpt_split IC'.
    zstep. zstep. zstep.
    call memset_callv; [exact DST'| lia| lia| lia| exact MI'|].
    do 11 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with ST1 : stk asegs mm lo _ |- _ =>
      lazymatch goal with ST3 : stk asegs mm (bv_unsigned sp + -2144) _ |- _ =>
      lazymatch goal with FR3 : rw_cells asegs mm (bv_unsigned sp + -64) _ |- _ =>
        pose proof (stk_merge asegs mm _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end end end.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ims_region : forall x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    0 < n ->
    evt asegs POST (ST_ 0x539fc m1 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros N0.
    pose proof R47 as RB. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    (nelimp AF1 8%nat; intros MI' IC' ST' FR' DST' MU' WM' ST2).
    pose proof IC' as IC2.
    pose proof (munch_refl [(bv_unsigned sp - 2224, bv_unsigned sp - 2144)] m1) as MU1.
    do 5 zstep.
    callsp region_is_poisoned_ok;
      [ exact IC' | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact AR | apply SO; exact N0 | ].
    do 5 zstep. fold_lits. sh_if_true.
    apply ims_call.
    lazymatch goal with |- ims_frame ?mm =>
      lazymatch goal with MUc : munch _ m1 mm |- _ =>
        assert (IC3 : icpt_cells mm)
          by (eapply icpt_cells_munch; [exact IC2| exact MUc|];
              unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)
      end end.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ims_7a8 : forall x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x539c0 m1 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros. pose proof R47 as RB.
    zstep. if_cases K; zify_cond K.
    - apply ims_region. lia.
    - zstep. apply ims_call. exact AF1.
  Qed.

  (* [comment removed for export] *)
  Lemma ims_7dc : forall x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    0 < n ->
    evt asegs POST (ST_ 0x539f4 m1 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros N0. pose proof R47 as RB.
    zstep. zstep. if_cases K.
    - apply ims_call. exact AF1.
    - apply ims_region. exact N0.
  Qed.

  (* [comment removed for export] *)
  Lemma ims_slow_loop : forall (k : nat) (i : Z) x1 x5 x6 x7 x9 (acc : word) x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    0 < n ->
    Z.to_nat (SH (d + n - 1) - SH d - i) = k -> 0 <= i -> SH d + i < SH (d + n - 1) ->
    evt asegs POST (ST_ 0x539e4 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 (2147450880 + d / 8 + i)) (Z_to_bv 64 (2147450880 + (d + n - 1) / 8)) acc x16 x17
                        x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros i x1 x5 x6 x7 x9 acc x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 N0 Hk Hi Hlt;
      pose proof R47 as RB; pose proof (SH_bounds d ltac:(lia)) as B1; pose proof (SH_bounds (d + n - 1) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    (* [comment removed for export] *)
    assert (V : exists b, m1 (wa (2147450880 + d / 8 + i)) = Some b).
    { destruct (m1 (wa (2147450880 + d / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 (SO N0) (2147450880 + d / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 m1 _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - replace (2147450880 + d / 8 + i + 1) with (2147450880 + d / 8 + (i + 1)) by lia.
      apply (IH (i + 1)); lia.
    - replace (2147450880 + d / 8 + i + 1) with (2147450880 + (d + n - 1) / 8) by lia.
      apply ims_7dc. exact N0.
  Qed.

  (* [comment removed for export] *)
  Lemma ims_slow : forall x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    0 < n ->
    evt asegs POST (ST_ 0x539c8 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 (2147450880 + d / 8)) (Z_to_bv 64 (2147450880 + (d + n - 1) / 8))
                        (Z_to_bv 64 (d + n - 1)) x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros N0. pose proof R47 as RB.
    pose proof (SH_bounds d ltac:(lia)) as B1. pose proof (SH_bounds (d + n - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    (nelim (shadow_ok_shb m1 d n (n - 1) (SO N0) ltac:(lia)) 3%nat; intros ve SHE Ce).
    replace (d + (n - 1)) with (d + n - 1) in SHE, Ce by lia.
    pose proof (shb_load_div' m1 (d + n - 1) ve (d + n - 1) SHE eq_refl ltac:(lia)) as RD.
    step. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases K; zify_cond K.
    - apply ims_7dc. exact N0.
    - replace (2147450880 + d / 8) with (2147450880 + d / 8 + 0) by lia.
      eapply (ims_slow_loop (Z.to_nat (SH (d + n - 1) - SH d - 0)) 0); unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ims_quick : forall x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    0 < n <= 64 ->
    evt asegs POST (ST_ 0x53874 m1 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros N64. pose proof R47 as RB.
    pose proof (SH_bounds d ltac:(lia)) as B1. pose proof (SH_bounds (d + n - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    (nelimp AF1 8%nat; intros MI' IC' ST' FR' DST' MU' WM' ST2).
    pose proof IC' as IC2. icpt_split IC'.
    do 9 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    replace (d + n + -1) with (d + n - 1) by lia.
    zstep. zstep. rewrite !land_m8 by lia.
    (* [comment removed for export] *)
    destruct (vis_read8 m1 ((2147450880 + d / 8) / 8 * 8)) as (w1 & L1 & W1). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 (SO ltac:(lia))). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 m1 ((2147450880 + (d + n - 1) / 8) / 8 * 8)) as (w2 & L2 & W2). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 (SO ltac:(lia))). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases K.
    - apply ims_slow. lia.
    - apply ims_call. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ims_body : forall x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x53848 m1 rae x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros. pose proof R47 as RB. pose proof STKv as SE.
    (nelimp AF1 8%nat; intros MI' IC' ST' FR' DST' MU' WM' ST2).
    pose proof IC' as IC2. icpt_split IC'.
    do 4 zstep. fold_lits. sh_if_false.
    do 4 zstep. fold_lits. rewrite (zb_lxor_ones d) by lia. sh_if_false.
    do 3 zstep. fold_lits.
    destruct (Z.eq_dec n 0) as [N0|N0].
    { sh_if_true. apply ims_7a8. }
    destruct (Z.lt_ge_cases 64 n) as [N64|N64].
    { sh_if_true. apply ims_7a8. }
    sh_if_false. apply ims_quick. lia.
  Qed.
End MemsetIcpt.

Lemma memset_icpt_ok : memset_icpt_spec.
Proof.
  unfold memset_icpt_spec, memset_contract.
  intros until lo. intros IC MI ST CEIL SPB -> -> -> HC DST HN AR WR SO SEP.
  pose proof (app_range_lt47 d n AR) as RB. pose proof (bv_unsigned_in_range 64 sp) as RSP.
  assert (SE : AINTRIN_STACK = 2304) by reflexivity.
  pose proof (munch_refl [(d, d + n); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (conj IC SO) as PK.
  unfold AMEMSET_T.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 11 zstep.
  destruct PK as [IC0 SO0]. clear IC SO.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
  assert (IC1 : icpt_cells m0);
  [ eapply icpt_cells_munch_wr; [exact IC0| exact MU| exact WR|];
    pose proof CEIL as CE; unfold alloc_ceiling, sp_window_lo, stack_max_size in CE; lia |];
  assert (SO1 : 0 < n -> shadow_ok m0 d n);
  [ intros N0; pose proof CEIL as CE; unfold alloc_ceiling, sp_window_lo, stack_max_size in CE;
    pose proof (SH_bounds d ltac:(lia)) as B1; pose proof (SH_bounds (d + n - 1) ltac:(lia)) as B2;
    eapply shadow_ok_munch; [exact (SO0 N0)| exact MU| exact N0| lia| lia|];
    cbn; unfold SH, SHADOW_OFFSET in *;
    destruct AR as [AR'|AR']; unfold lowmem_range, highmem_range, KHIGHMEM_BEG, KHIGHMEM_END, KLOWSHADOW_BEG in AR';
      Z.div_mod_to_equations; lia |];
  destruct (stk_split asegs m0 lo (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ST ltac:(lia)) as [ST1 ST2]
  end.
  eapply ims_body; try eassumption.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); eassumption.
Qed.




End CeilWrap.
