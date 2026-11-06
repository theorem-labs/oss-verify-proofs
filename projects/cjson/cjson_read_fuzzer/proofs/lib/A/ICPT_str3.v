(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_strlen.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module ICPT_str.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_strlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_mem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asan_inited_ok :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  icpt_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m (seg_rom asegs)
                        /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AASAN_INITED_FN) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros IC MI. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  icpt_split IC. unfold AASAN_INITED_FN.
  do 5 zstep. fold_lits. zstep.
  apply evt_done. split; [reflexivity| auto].
Qed.

(* [comment removed for export] *)
Lemma try_init_ok :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  icpt_cells m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  evt asegs (fun ms' => exists m',
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATRY_INIT) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros IC MI ST CEIL SPB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold alloc_ceiling, sp_window_lo, stack_max_size in CEIL.
  pose proof (conj IC I) as PK.
  unfold ATRY_INIT. carve_frame 16%nat ST.
  do 3 zstep.
  destruct PK as [IC' _].
  assert (IC1 : forall mm, munch [(bv_unsigned sp - 16, bv_unsigned sp)] m mm -> icpt_cells mm).
  { intros mm MUm. eapply icpt_cells_munch; [exact IC'| exact MUm|]. unfold icpt_cell_ivs.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (IC1 mm ltac:(assumption)) as IC2 end.
  icpt_split IC2.
  do 5 zstep. fold_lits. zstep. fold_lits. sh_if_false.
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with FR : rw_cells asegs mm _ _ |- _ =>
    lazymatch goal with ST' : stk asegs mm lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end end end.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition strlen_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).

Lemma strlen_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S : Z) (str slack : list byte),
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> 0 <= S < 2^64 -> mem_inv asegs m ->
  evt asegs (strlen_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9b840) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros BA NN PAD HS MI.
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply strlen_spec; rewrite ?ES; [exact BA | exact NN | exact PAD | exact MI]. }
  intros ms' P. unfold strlen_post, strlen_postv in *. rewrite ES in P. exact P.
Qed.

Section StrlenIcpt.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (s lo : Z) (str slack : list byte).
  Let L := Z.of_nat (length str).
  Hypothesis HL : L + 1 < 2^40.
  Hypothesis AR : app_range s (L + 1).
  Hypothesis NN : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : (- (s + L + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + ASTRFN_STACK <= bv_unsigned sp.
  Hypothesis SEP : s + L + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s.

  Lemma RB : 0 <= s /\ s + (L + 1) < 2^47. Proof. exact (app_range_lt47 s (L + 1) AR). Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv : ASTRFN_STACK = 2400. Proof. reflexivity. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (strlen_icpt_post rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 F fc s str slack lo m).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
            x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition ast_frame (mm : word -> option byte) : Prop :=
    mem_inv asegs mm /\ icpt_cells mm /\ stk asegs mm lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs mm (bv_unsigned sp + -64) [C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ bytes_at asegs mm s (str ++ Z_to_bv 8 0 :: slack)
    /\ munch [(bv_unsigned sp - ASTRFN_STACK, bv_unsigned sp)] m mm /\ wmono asegs m mm
    /\ stk asegs mm (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ shadow_ok mm s (L + 1).

  Ltac ast_intro AF := (nelim AF 9%nat; intros MI' IC' ST' FR' STR' MU' WM' ST2 SO).
  Ltac ast_pack := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); assumption.

  (* [comment removed for export] *)
  Lemma ast_after_callee : forall mm mm' k,
    icpt_cells mm -> shadow_ok mm s (L + 1) -> 0 <= k <= 80 ->
    munch [(bv_unsigned sp - 2144 - k, bv_unsigned sp - 2144)] mm mm' ->
    icpt_cells mm' /\ shadow_ok mm' s (L + 1).
  Proof.
    intros mm mm' k IC SO Hk MUr. pose proof RB. pose proof CEILv. pose proof STKv.
    split.
    - eapply icpt_cells_munch; [exact IC| exact MUr|]. unfold icpt_cell_ivs.
      repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - pose proof (SH_bounds s ltac:(lia)). pose proof (SH_bounds (s + (L + 1) - 1) ltac:(lia)).
      eapply shadow_ok_munch; [exact SO| exact MUr| lia| lia| lia|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ast_ret : forall mm x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    ast_frame mm ->
    evt asegs POST (ST_ 0x42624 mm x1 x5 x6 x7 x9 (Z_to_bv 64 L) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. ast_intro AF.
    pose proof RB as RB'. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    do 11 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with ST1 : stk asegs mm2 lo _ |- _ =>
      lazymatch goal with ST3 : stk asegs mm2 (bv_unsigned sp + -2144) _ |- _ =>
      lazymatch goal with FR3 : rw_cells asegs mm2 (bv_unsigned sp + -64) _ |- _ =>
        pose proof (stk_merge asegs mm2 _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end end end.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ast_62144 : forall mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31,
    ast_frame mm ->
    evt asegs POST (ST_ 0x427f8 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 (Z_to_bv 64 L) x22 x28 x29 x30 x31).
  Proof. intros until x31. intros AF. pose proof RB as RB'. zstep. zstep. apply ast_ret. exact AF. Qed.

  (* [comment removed for export] *)
  Lemma ast_region : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31,
    ast_frame mm ->
    evt asegs POST (ST_ 0x42734 mm x1 x5 x6 x7 (Z_to_bv 64 (L + 1)) x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 (Z_to_bv 64 L) x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. ast_intro AF.
    pose proof RB as RB'. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof IC' as IC2. pose proof SO as SO2.
    pose proof (munch_refl [(bv_unsigned sp - 2144 - 80, bv_unsigned sp - 2144)] mm) as MU1.
    do 3 zstep.
    callsp region_is_poisoned_ok;
      [ exact IC' | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact AR | exact SO | ].
    zstep. fold_lits. sh_if_true.
    apply ast_62144.
    lazymatch goal with |- ast_frame ?mm2 =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
        destruct (ast_after_callee mm mm2 80 IC2 SO2 ltac:(lia) MUc) as [IC3 SO3]
      end end.
    ast_pack.
  Qed.

  (* [comment removed for export] *)
  Lemma ast_62078 : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31,
    ast_frame mm ->
    evt asegs POST (ST_ 0x4272c mm x1 x5 x6 x7 (Z_to_bv 64 (L + 1)) x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 (Z_to_bv 64 L) x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'.
    zstep. zstep. if_cases K.
    - apply ast_62144. exact AF.
    - apply ast_region. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma ast_loop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 (acc : word) x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31,
    ast_frame mm ->
    Z.to_nat (SH (s + L) - SH s - i) = k -> 0 <= i -> SH s + i < SH (s + L) ->
    evt asegs POST (ST_ 0x4271c mm x1 x5 x6 x7 (Z_to_bv 64 (L + 1)) acc (Z_to_bv 64 (2147450880 + s / 8 + i)) (Z_to_bv 64 (2147450880 + (s + L) / 8))
                        x13 x14 x15 x16 x17 x19 x20 (Z_to_bv 64 L) x22 x28 x29 x30 x31).
  Proof.
    intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 acc x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31 AF Hk Hi Hlt;
      pose proof RB as RB'; pose proof (SH_bounds s ltac:(lia)) as B1; pose proof (SH_bounds (s + L) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    pose proof AF as AF'. ast_intro AF'.
    assert (V : exists b, mm (wa (2147450880 + s / 8 + i)) = Some b).
    { destruct (mm (wa (2147450880 + s / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 SO (2147450880 + s / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - replace (2147450880 + s / 8 + i + 1) with (2147450880 + s / 8 + (i + 1)) by lia.
      apply (IH (i + 1)); try assumption; lia.
    - replace (2147450880 + s / 8 + i + 1) with (2147450880 + (s + L) / 8) by lia.
      apply ast_62078. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma ast_slow : forall mm x1 x5 x6 x7 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    ast_frame mm ->
    evt asegs POST (ST_ 0x426fc mm x1 x5 x6 x7 (Z_to_bv 64 (L + 1)) (Z_to_bv 64 L) (Z_to_bv 64 (2147450880 + s / 8)) (Z_to_bv 64 (2147450880 + (s + L) / 8))
                        (Z_to_bv 64 (s + L)) x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'.
    pose proof (SH_bounds s ltac:(lia)) as B1. pose proof (SH_bounds (s + L) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. ast_intro AF'.
    (nelim (shadow_ok_shb mm s (L + 1) L SO ltac:(lia)) 3%nat; intros ve SHE Ce).
    pose proof (shb_load_div' mm (s + L) ve (s + L) SHE eq_refl ltac:(lia)) as RD.
    zstep. step. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases K; zify_cond K.
    - apply ast_62078. exact AF.
    - replace (2147450880 + s / 8) with (2147450880 + s / 8 + 0) by lia.
      eapply (ast_loop mm (Z.to_nat (SH (s + L) - SH s - 0)) 0); try exact AF; unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ast_62038 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    ast_frame mm ->
    evt asegs POST (ST_ 0x426ec mm x1 x5 x6 x7 (Z_to_bv 64 (L + 1)) (Z_to_bv 64 L) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'.
    zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
    apply ast_region. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma ast_quick : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    ast_frame mm -> L < 64 ->
    evt asegs POST (ST_ 0x425ec mm x1 x5 x6 x7 (Z_to_bv 64 (L + 1)) (Z_to_bv 64 L) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HL64. pose proof RB as RB'.
    pose proof (SH_bounds s ltac:(lia)) as B1. pose proof (SH_bounds (s + L) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. ast_intro AF'.
    icpt_split IC'.
    do 8 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    replace (L + s) with (s + L) by lia.
    zstep. zstep. rewrite !land_m8 by lia.
    destruct (vis_read8 mm ((2147450880 + s / 8) / 8 * 8)) as (w1 & L1 & W1). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 SO). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 mm ((2147450880 + (s + L) / 8) / 8 * 8)) as (w2 & L2 & W2). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 SO). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases K.
    - apply ast_slow. exact AF.
    - apply ast_ret. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma ast_body : forall mm x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31,
    ast_frame mm ->
    evt asegs POST (ST_ 0x4259c mm rae x5 x6 x7 x9 (Z_to_bv 64 s) x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof AF as AF'. ast_intro AF'. pose proof IC' as IC2. pose proof SO as SO2.
    zstep.
    call asan_inited_ok; [exact IC'| exact MI'|].
    zstep. sh_if_false.
    pose proof (munch_refl [(bv_unsigned sp - 2144 - 16, bv_unsigned sp - 2144)] mm) as MU1.
    zstep. callsp try_init_ok; [exact IC'| exact MI'| exact ST'| exact CEIL| lia|].
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
        destruct (ast_after_callee mm mm2 16 IC2 SO2 ltac:(lia) MUc) as [IC3 SO3]; clear MUc
      end end.
    pose proof IC3 as IC4. icpt_split IC4.
    do 5 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) => pose proof (munch_refl [] mm2) as MU0 end.
    call strlen_callv; [eassumption| exact NN| exact PAD| lia| eassumption|].
    lazymatch type of MU0 with munch [] ?mm2 ?mm3 =>
      assert (IC5 : icpt_cells mm3) by
        (eapply icpt_cells_munch; [exact IC3| exact MU0| apply Forall_forall; intros; exact I]);
      assert (SO5 : shadow_ok mm3 s (L + 1)) by
        (eapply shadow_ok_munch; [exact SO3| exact MU0| lia| | | exact I];
         pose proof (SH_bounds s ltac:(lia)); pose proof (SH_bounds (s + (L + 1) - 1) ltac:(lia)); lia)
    end.
    zstep. fold_lits. sh_if_false.
    do 3 zstep. fold_lits.
    zstep. sh_if_false.
    do 5 zstep. fold_lits. rewrite (zb_lxor_ones s) by lia. sh_if_false.
    zstep. zstep.
    if_cases K; zify_cond K.
    - apply ast_62038. ast_pack.
    - apply ast_quick; [ast_pack| unfold L; lia].
  Qed.
End StrlenIcpt.

Lemma strlen_icpt_ok : strlen_icpt_spec.
Proof.
  unfold strlen_icpt_spec.
  intros until lo. intros IC MI ST CEIL SPB -> STR NN PAD HL AR SO SEP.
  pose proof (app_range_lt47 _ _ AR) as RB. pose proof (bv_unsigned_in_range 64 sp) as RSP.
  assert (SE : ASTRFN_STACK = 2400) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - ASTRFN_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (conj IC (conj SO STR)) as PK.
  unfold ASTRLEN_T.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 12 zstep.
  (nelim PK 3%nat; intros IC0 SO0 STR0). clear IC SO.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
  assert (IC1 : icpt_cells m0);
  [ eapply icpt_cells_munch; [exact IC0| exact MU|]; unfold icpt_cell_ivs;
    repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil |];
  assert (SO1 : shadow_ok m0 s (Z.of_nat (length str) + 1));
  [ pose proof (SH_bounds s ltac:(lia)) as B1; pose proof (SH_bounds (s + (Z.of_nat (length str) + 1) - 1) ltac:(lia)) as B2;
    eapply shadow_ok_munch; [exact SO0| exact MU| lia| lia| lia|]; cbn; lia |];
  assert (STR1 : bytes_at asegs m0 s (str ++ Z_to_bv 8 0 :: slack));
  [ eapply bytes_at_transport; [exact STR0| exact MU|]; cbn; rewrite length_app; cbn; lia |];
  destruct (stk_split asegs m0 lo (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ST ltac:(lia)) as [ST1 ST2]
  end.
  eapply ast_body; try eassumption; try lia.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); eassumption.
Qed.




End CeilWrap.
End ICPT_str.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module ICPT_str2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_mem ICPT_str.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition prefix_eq (x y : list Z) (j : nat) : Prop :=
  forall k a b, (k < j)%nat -> nth_error x k = Some a -> nth_error y k = Some b -> a = b /\ a <> 0.

Lemma strncmp_facts_stop : forall x y n j a b,
  (j < n)%nat -> nth_error x j = Some a -> nth_error y j = Some b ->
  (forall k, (k < j)%nat -> exists c, nth_error x k = Some c /\ nth_error y k = Some c /\ c <> 0) ->
  (a = 0 \/ a <> b) ->
  strncmp_stop x y n = j /\ strncmp_spec x y n = (if a =? b then 0 else if a <? b then -1 else 1).
Proof.
  intros x y n j. revert x y n.
  induction j as [|j IH]; intros x y n a b Hj Ha Hb HP Hs.
  - destruct n as [|n']; [lia|]. destruct x as [|a' x']; [discriminate|]. destruct y as [|b' y']; [discriminate|].
    cbn in Ha, Hb. inversion Ha; inversion Hb; subst. cbn.
    destruct (Z.eqb_spec a b).
    + subst. destruct Hs as [->|]; [cbn; auto| congruence].
    + cbn. auto.
  - destruct n as [|n']; [lia|]. destruct x as [|a' x']; [discriminate|]. destruct y as [|b' y']; [discriminate|].
    (nelim (HP O ltac:(lia)) 4%nat; intros c Hc1 Hc2 Hc0). cbn in Hc1, Hc2. inversion Hc1; inversion Hc2; subst.
    cbn. rewrite Z.eqb_refl. destruct (Z.eqb_spec c 0); [lia|]. cbn.
    destruct (IH x' y' n' a b ltac:(lia) Ha Hb) as [E1 E2]; [| exact Hs|].
    { intros k Hk. (nelim (HP (S k) ltac:(lia)) 4%nat; intros c' H1 H2 H3). exists c'. cbn in H1, H2. auto. }
    rewrite E1, E2. auto.
Qed.

Lemma strncmp_facts_all : forall x y n,
  (forall k, (k < n)%nat -> exists c, nth_error x k = Some c /\ nth_error y k = Some c /\ c <> 0) ->
  strncmp_stop x y n = n /\ strncmp_spec x y n = 0.
Proof.
  intros x y n. revert x y. induction n as [|n IH]; intros x y HP.
  { destruct x; destruct y; split; reflexivity. }
  (nelim (HP O ltac:(lia)) 4%nat; intros c H1 H2 H3).
  destruct x as [|a x']; [discriminate|]. destruct y as [|b y']; [discriminate|]. cbn in H1, H2. inversion H1; inversion H2; subst.
  cbn. rewrite Z.eqb_refl. destruct (Z.eqb_spec c 0); [lia|]. cbn.
  destruct (IH x' y') as [E1 E2].
  { intros k Hk. (nelim (HP (S k) ltac:(lia)) 4%nat; intros c' A1 A2 A3). exists c'. cbn in A1, A2. auto. }
  rewrite E1, E2. auto.
Qed.

Lemma strncmp_stop_le : forall x y n, (strncmp_stop x y n <= n)%nat.
Proof.
  intros x y n. revert x y. induction n as [|n IH]; intros x y.
  - destruct x; destruct y; cbn; lia.
  - destruct x as [|a x']; [cbn; lia|]. destruct y as [|b y']; [cbn; lia|]. cbn.
    destruct ((a =? b) && negb (a =? 0)); [| lia]. specialize (IH x' y'). lia.
Qed.

Lemma strncmp_stop_ge : forall x y n j,
  (forall k, (k < j)%nat -> exists c, nth_error x k = Some c /\ nth_error y k = Some c /\ c <> 0) ->
  (j <= n)%nat -> (j <= strncmp_stop x y n)%nat.
Proof.
  intros x y n j. revert x y n. induction j as [|j IH]; intros x y n HP Hj; [lia|].
  destruct n as [|n']; [lia|].
  (nelim (HP O ltac:(lia)) 4%nat; intros c H1 H2 H3).
  destruct x as [|a x']; [discriminate|]. destruct y as [|b y']; [discriminate|]. cbn in H1, H2. inversion H1; inversion H2; subst.
  cbn. rewrite Z.eqb_refl. destruct (Z.eqb_spec c 0); [lia|]. cbn.
  enough (j <= strncmp_stop x' y' n')%nat by lia.
  apply IH; [| lia]. intros k Hk. (nelim (HP (S k) ltac:(lia)) 4%nat; intros c' A1 A2 A3). exists c'. cbn in A1, A2. auto.
Qed.

Section StrncmpIcpt.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (p q n lo : Z) (x y : list byte).
  Variables (iz r : Z).
  Hypothesis HN : 0 <= n < 2^40.
  Hypothesis Hiz : iz = Z.of_nat (strncmp_stop (map bv_unsigned x) (map bv_unsigned y) (Z.to_nat n)).
  Hypothesis Hr : r = Z.min (iz + 1) n.
  Hypothesis LX : Z.of_nat (length x) = r.
  Hypothesis LY : Z.of_nat (length y) = r.
  Hypothesis ARP : app_range p r.
  Hypothesis ARQ : app_range q r.

  Lemma RP : 0 <= p /\ p + r < 2^47. Proof. exact (app_range_lt47 _ _ ARP). Qed.
  Lemma RQ : 0 <= q /\ q + r < 2^47. Proof. exact (app_range_lt47 _ _ ARQ). Qed.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + ASTRFN_STACK <= bv_unsigned sp.
  Hypothesis SEPP : p + r <= lo \/ bv_unsigned sp <= p.
  Hypothesis SEPQ : q + r <= lo \/ bv_unsigned sp <= q.

  Lemma Hir : 0 <= iz <= n /\ 0 <= r <= n /\ r <= iz + 1.
  Proof. pose proof (strncmp_stop_le (map bv_unsigned x) (map bv_unsigned y) (Z.to_nat n)). subst r iz. lia. Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv : ASTRFN_STACK = 2400. Proof. reflexivity. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation SPECV := (strncmp_spec (map bv_unsigned x) (map bv_unsigned y) (Z.to_nat n)).
  #[warnings="-notation-for-abbreviation"]
  Notation POST := (strncmp_icpt_post rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc x y n lo m).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2176)) gp tp x5 x6 x7 sp (Z_to_bv 64 n)
            x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 q) (Z_to_bv 64 p) rae x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition asn_frame (mm : word -> option byte) : Prop :=
    mem_inv asegs mm /\ icpt_cells mm /\ stk asegs mm lo (bv_unsigned sp + -2176)
    /\ rw_cells asegs mm (bv_unsigned sp + -104)
         [C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ bytes_at asegs mm p x /\ bytes_at asegs mm q y
    /\ munch [(bv_unsigned sp - ASTRFN_STACK, bv_unsigned sp)] m mm /\ wmono asegs m mm
    /\ stk asegs mm (bv_unsigned sp + -2176) (bv_unsigned sp + -104)
    /\ (0 < n -> shadow_ok mm p r) /\ (0 < n -> shadow_ok mm q r).

  Ltac asn_intro AF := (nelim AF 11%nat; intros MI' IC' ST' FR' X' Y' MU' WM' ST2 SOP SOQ).
  Ltac asn_pack := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); assumption.

  Lemma asn_after_callee : forall mm mm' k,
    icpt_cells mm -> (0 < n -> shadow_ok mm p r) -> (0 < n -> shadow_ok mm q r) -> 0 <= k <= 80 ->
    munch [(bv_unsigned sp - 2176 - k, bv_unsigned sp - 2176)] mm mm' ->
    icpt_cells mm' /\ (0 < n -> shadow_ok mm' p r) /\ (0 < n -> shadow_ok mm' q r).
  Proof.
    intros mm mm' k IC SOP SOQ Hk MUr. pose proof Hir. pose proof CEILv. pose proof STKv. pose proof RP. pose proof RQ.
    split; [| split].
    - eapply icpt_cells_munch; [exact IC| exact MUr|]. unfold icpt_cell_ivs.
      repeat (apply Forall_cons; [cbn; (lia_on CEIL SPB Hk H1)|]). apply Forall_nil.
    - intros N0. pose proof (SH_bounds p ltac:(lia)). pose proof (SH_bounds (p + r - 1) ltac:(lia)).
      assert (0 < r) by (subst r; lia).
      eapply shadow_ok_munch; [exact (SOP N0)| exact MUr| lia| lia| lia|]. cbn. lia.
    - intros N0. pose proof (SH_bounds q ltac:(lia)). pose proof (SH_bounds (q + r - 1) ltac:(lia)).
      assert (0 < r) by (subst r; lia).
      eapply shadow_ok_munch; [exact (SOQ N0)| exact MUr| lia| lia| lia|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma asn_ret : forall mm (c1 c2 : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31,
    asn_frame mm -> 0 <= c1 < 256 -> 0 <= c2 < 256 ->
    SPECV = (if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1) ->
    evt asegs POST (ST_ 0x4321c mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 (Z_to_bv 64 c1) (Z_to_bv 64 c2) x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HC1 HC2 RES. asn_intro AF.
    pose proof Hir as HIR. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    do 10 zstep.
    do 17 zstep.
    replace (Z.b2z (c2 <? c1) - Z.b2z (c1 <? c2)) with SPECV.
    2:{ rewrite RES. destruct (Z.eqb_spec c1 c2); [subst; rewrite Z.ltb_irrefl; reflexivity|].
        destruct (Z.ltb_spec c1 c2); destruct (Z.ltb_spec c2 c1); cbn; lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with ST1 : stk asegs mm2 lo _ |- _ =>
      lazymatch goal with ST3 : stk asegs mm2 (bv_unsigned sp + -2176) _ |- _ =>
      lazymatch goal with FR3 : rw_cells asegs mm2 (bv_unsigned sp + -104) _ |- _ =>
        pose proof (stk_merge asegs mm2 _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end end end.
    finish.
  Qed.

  (* [comment removed for export] *)
  Section QPhase.
    Variables (c1 c2 : Z).
    Hypothesis HC1 : 0 <= c1 < 256.
    Hypothesis HC2 : 0 <= c2 < 256.
    Hypothesis RES : SPECV = (if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1).

    #[warnings="-notation-for-abbreviation"]
    Notation STQ pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 x27 x28 x29 x30 x31 :=
      (ST_ pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 (Z_to_bv 64 c1) (Z_to_bv 64 c2) x26 x27 x28 x29 x30 x31).

    (* [comment removed for export] *)
    Lemma asn_qregion : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31,
      asn_frame mm -> 0 < r ->
      evt asegs POST (STQ 0x43498 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x27 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF R0. asn_intro AF.
      pose proof Hir as HIR. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
      assert (N0 : 0 < n) by lia.
      pose proof IC' as IC2. pose proof SOP as SOP2. pose proof SOQ as SOQ2.
      pose proof (munch_refl [(bv_unsigned sp - 2176 - 80, bv_unsigned sp - 2176)] mm) as MU1.
      do 3 zstep.
      callsp region_is_poisoned_ok;
        [ exact IC' | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
        | exact ARQ | exact (SOQ N0) | ].
      zstep. fold_lits. sh_if_true.
      apply asn_ret; [| exact HC1| exact HC2| exact RES].
      lazymatch goal with |- asn_frame ?mm2 =>
        lazymatch goal with MUc : munch _ mm mm2 |- _ =>
          (nelim (asn_after_callee mm mm2 80 IC2 SOP2 SOQ2 ltac:(lia) MUc) 3%nat; intros IC3 SOP3 SOQ3)
        end end.
      asn_pack.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_q278 : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31,
      asn_frame mm ->
      evt asegs POST (STQ 0x43300 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x27 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF. pose proof Hir as HIR.
      zstep. if_cases K; zify_cond K.
      - apply asn_qregion; [exact AF| lia].
      - zstep. apply asn_ret; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_q408 : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31,
      asn_frame mm -> 0 < r ->
      evt asegs POST (STQ 0x43490 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x27 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF R0. pose proof Hir as HIR.
      zstep. zstep. if_cases K.
      - apply asn_ret; assumption.
      - apply asn_qregion; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_qloop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 (acc : word) x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31,
      asn_frame mm -> 0 < r ->
      Z.to_nat (SH (q + r - 1) - SH q - i) = k -> 0 <= i -> SH q + i < SH (q + r - 1) ->
      evt asegs POST (STQ 0x43480 mm x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + q / 8 + i)) (Z_to_bv 64 (2147450880 + (q + r - 1) / 8)) acc
                          x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x27 x28 x29 x30 x31).
    Proof.
      intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 acc x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31 AF R0 Hk Hi Hlt;
        pose proof RQ as RB; pose proof (SH_bounds q ltac:(lia)) as B1; pose proof (SH_bounds (q + r - 1) ltac:(lia)) as B2;
        unfold SH, SHADOW_OFFSET in *; [lia|].
      pose proof AF as AF'. asn_intro AF'. assert (N0 : 0 < n) by (pose proof Hir; lia).
      assert (V : exists b, mm (wa (2147450880 + q / 8 + i)) = Some b).
      { destruct (mm (wa (2147450880 + q / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
        apply (proj2 (SOQ N0) (2147450880 + q / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
      destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
      zstep. zstep. zstep. zstep.
      if_cases K; zify_cond K.
      - replace (2147450880 + q / 8 + i + 1) with (2147450880 + q / 8 + (i + 1)) by lia.
        apply (IH (i + 1)); try assumption; lia.
      - replace (2147450880 + q / 8 + i + 1) with (2147450880 + (q + r - 1) / 8) by lia.
        apply asn_q408; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_qslow : forall mm x1 x5 x6 x7 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31,
      asn_frame mm -> 0 < r ->
      evt asegs POST (STQ 0x43464 mm x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + q / 8)) (Z_to_bv 64 (2147450880 + (q + r - 1) / 8)) (Z_to_bv 64 (q + r - 1))
                          x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x27 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF R0. pose proof RQ as RB.
      pose proof (SH_bounds q ltac:(lia)) as B1. pose proof (SH_bounds (q + r - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
      pose proof AF as AF'. asn_intro AF'. assert (N0 : 0 < n) by (pose proof Hir; lia).
      (nelim (shadow_ok_shb mm q r (r - 1) (SOQ N0) ltac:(lia)) 3%nat; intros ve SHE Ce).
      replace (q + (r - 1)) with (q + r - 1) in SHE, Ce by lia.
      pose proof (shb_load_div' mm (q + r - 1) ve (q + r - 1) SHE eq_refl ltac:(lia)) as RD.
      step. clear RD.
      rewrite (sxb_zb_small ve) by lia.
      do 5 zstep.
      zstep. if_cases K; zify_cond K.
      - apply asn_q408; assumption.
      - replace (2147450880 + q / 8) with (2147450880 + q / 8 + 0) by lia.
        eapply (asn_qloop mm (Z.to_nat (SH (q + r - 1) - SH q - 0)) 0); try exact AF; try exact R0; unfold SH, SHADOW_OFFSET; try lia.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_qquick : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31,
      asn_frame mm -> 0 < r <= 64 ->
      evt asegs POST (STQ 0x431e0 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x27 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF R64. pose proof RQ as RB.
      pose proof (SH_bounds q ltac:(lia)) as B1. pose proof (SH_bounds (q + r - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
      pose proof AF as AF'. asn_intro AF'. assert (N0 : 0 < n) by (pose proof Hir; lia).
      icpt_split IC'.
      do 9 zstep.
      rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
      replace (q + r + -1) with (q + r - 1) by lia.
      zstep. zstep. rewrite !land_m8 by lia.
      destruct (vis_read8 mm ((2147450880 + q / 8) / 8 * 8)) as (w1 & L1 & W1). (* [comment removed for export] *)
      { intros j Hj. apply (proj2 (SOQ N0)). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
      { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
      destruct (vis_read8 mm ((2147450880 + (q + r - 1) / 8) / 8 * 8)) as (w2 & L2 & W2). (* [comment removed for export] *)
      { intros j Hj. apply (proj2 (SOQ N0)). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
      { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
      unfold wa in W1, W2.
      step. step. clear W1 W2.
      zstep. step. if_cases K.
      - apply asn_qslow; [exact AF| lia].
      - apply asn_ret; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_q14c : forall mm r' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31,
      asn_frame mm -> r' = r ->
      evt asegs POST (STQ 0x431d4 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r') x22 x23 x26 x27 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF ->. pose proof Hir as HIR.
      zstep. zstep. zstep. fold_lits.
      destruct (Z.eq_dec r 0) as [R0|R0].
      { sh_if_true. apply asn_q278. exact AF. }
      destruct (Z.lt_ge_cases 64 r) as [R64|R64].
      { sh_if_true. apply asn_q278. exact AF. }
      sh_if_false. apply asn_qquick; [exact AF| lia].
    Qed.

    (* [comment removed for export] *)
    Lemma asn_q13c : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 x28 x29 x30 x31,
      asn_frame mm ->
      evt asegs POST (STQ 0x431c4 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 (Z_to_bv 64 iz) x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF. pose proof Hir as HIR. pose proof RQ as RB.
      zstep. zstep. if_cases K1; zify_cond K1.
      - (* [comment removed for export] *)
        zstep. zstep. zstep. fold_lits. rewrite (zb_lxor_ones q) by lia. sh_if_true.
        apply asn_q14c; [exact AF| lia].
      - zstep. zstep. fold_lits. rewrite (zb_lxor_ones q) by lia. sh_if_false.
        apply asn_q14c; [exact AF| lia].
    Qed.

    (* [comment removed for export] *)
    #[warnings="-notation-for-abbreviation"]
    Notation STP pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 x28 x29 x30 x31 :=
      (STQ pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 (Z_to_bv 64 iz) x28 x29 x30 x31).

    (* [comment removed for export] *)
    Lemma asn_pregion : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31,
      asn_frame mm -> 0 < r ->
      evt asegs POST (STP 0x433d0 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF R0. asn_intro AF.
      pose proof Hir as HIR. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
      assert (N0 : 0 < n) by lia.
      pose proof IC' as IC2. pose proof SOP as SOP2. pose proof SOQ as SOQ2.
      pose proof (munch_refl [(bv_unsigned sp - 2176 - 80, bv_unsigned sp - 2176)] mm) as MU1.
      do 3 zstep.
      callsp region_is_poisoned_ok;
        [ exact IC' | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
        | exact ARP | exact (SOP N0) | ].
      zstep. fold_lits. sh_if_true.
      apply asn_q13c.
      lazymatch goal with |- asn_frame ?mm2 =>
        lazymatch goal with MUc : munch _ mm mm2 |- _ =>
          (nelim (asn_after_callee mm mm2 80 IC2 SOP2 SOQ2 ltac:(lia) MUc) 3%nat; intros IC3 SOP3 SOQ3)
        end end.
      asn_pack.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_p30c : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31,
      asn_frame mm ->
      evt asegs POST (STP 0x43394 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF. pose proof Hir as HIR.
      zstep. if_cases K; zify_cond K.
      - apply asn_pregion; [exact AF| lia].
      - zstep. apply asn_q13c. exact AF.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_p340 : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31,
      asn_frame mm -> 0 < r ->
      evt asegs POST (STP 0x433c8 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF R0. pose proof Hir as HIR.
      zstep. zstep. if_cases K.
      - apply asn_q13c. exact AF.
      - apply asn_pregion; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_ploop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 (acc : word) x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31,
      asn_frame mm -> 0 < r ->
      Z.to_nat (SH (p + r - 1) - SH p - i) = k -> 0 <= i -> SH p + i < SH (p + r - 1) ->
      evt asegs POST (STP 0x433b8 mm x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + p / 8 + i)) (Z_to_bv 64 (2147450880 + (p + r - 1) / 8)) acc
                          x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x28 x29 x30 x31).
    Proof.
      intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 acc x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31 AF R0 Hk Hi Hlt;
        pose proof RP as RB; pose proof (SH_bounds p ltac:(lia)) as B1; pose proof (SH_bounds (p + r - 1) ltac:(lia)) as B2;
        unfold SH, SHADOW_OFFSET in *; [lia|].
      pose proof AF as AF'. asn_intro AF'. assert (N0 : 0 < n) by (pose proof Hir; lia).
      assert (V : exists b, mm (wa (2147450880 + p / 8 + i)) = Some b).
      { destruct (mm (wa (2147450880 + p / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
        apply (proj2 (SOP N0) (2147450880 + p / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
      destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
      zstep. zstep. zstep. zstep.
      if_cases K; zify_cond K.
      - replace (2147450880 + p / 8 + i + 1) with (2147450880 + p / 8 + (i + 1)) by lia.
        apply (IH (i + 1)); try assumption; lia.
      - replace (2147450880 + p / 8 + i + 1) with (2147450880 + (p + r - 1) / 8) by lia.
        apply asn_p340; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_pslow : forall mm x1 x5 x6 x7 x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31,
      asn_frame mm -> 0 < r ->
      evt asegs POST (STP 0x4339c mm x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 (2147450880 + (p + r - 1) / 8)) (Z_to_bv 64 (p + r - 1))
                          x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF R0. pose proof RP as RB.
      pose proof (SH_bounds p ltac:(lia)) as B1. pose proof (SH_bounds (p + r - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
      pose proof AF as AF'. asn_intro AF'. assert (N0 : 0 < n) by (pose proof Hir; lia).
      (nelim (shadow_ok_shb mm p r (r - 1) (SOP N0) ltac:(lia)) 3%nat; intros ve SHE Ce).
      replace (p + (r - 1)) with (p + r - 1) in SHE, Ce by lia.
      pose proof (shb_load_div' mm (p + r - 1) ve (p + r - 1) SHE eq_refl ltac:(lia)) as RD.
      step. clear RD.
      rewrite (sxb_zb_small ve) by lia.
      do 5 zstep.
      zstep. if_cases K; zify_cond K.
      - apply asn_p340; assumption.
      - replace (2147450880 + p / 8) with (2147450880 + p / 8 + 0) by lia.
        eapply (asn_ploop mm (Z.to_nat (SH (p + r - 1) - SH p - 0)) 0); try exact AF; try exact R0; unfold SH, SHADOW_OFFSET; try lia.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_pquick : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31,
      asn_frame mm -> 0 < r <= 64 ->
      evt asegs POST (STP 0x43188 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x22 x23 x26 x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF R64. pose proof RP as RB.
      pose proof (SH_bounds p ltac:(lia)) as B1. pose proof (SH_bounds (p + r - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
      pose proof AF as AF'. asn_intro AF'. assert (N0 : 0 < n) by (pose proof Hir; lia).
      icpt_split IC'.
      do 9 zstep.
      rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
      replace (p + r + -1) with (p + r - 1) by lia.
      zstep. zstep. rewrite !land_m8 by lia.
      destruct (vis_read8 mm ((2147450880 + p / 8) / 8 * 8)) as (w1 & L1 & W1). (* [comment removed for export] *)
      { intros j Hj. apply (proj2 (SOP N0)). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
      { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
      destruct (vis_read8 mm ((2147450880 + (p + r - 1) / 8) / 8 * 8)) as (w2 & L2 & W2). (* [comment removed for export] *)
      { intros j Hj. apply (proj2 (SOP N0)). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
      { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
      unfold wa in W1, W2.
      step. step. clear W1 W2.
      zstep. step. if_cases K.
      - apply asn_pslow; [exact AF| lia].
      - apply asn_q13c. exact AF.
    Qed.

    (* [comment removed for export] *)
    Lemma asn_p0f4 : forall mm r' iz' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 x31,
      asn_frame mm -> r' = r -> iz' = iz ->
      evt asegs POST (STQ 0x4317c mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r') x22 x23 x26 (Z_to_bv 64 iz') x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF -> ->. pose proof Hir as HIR.
      zstep. zstep. zstep. fold_lits.
      destruct (Z.eq_dec r 0) as [R0|R0].
      { sh_if_true. apply asn_p30c. exact AF. }
      destruct (Z.lt_ge_cases 64 r) as [R64|R64].
      { sh_if_true. apply asn_p30c. exact AF. }
      sh_if_false. apply asn_pquick; [exact AF| lia].
    Qed.

    (* [comment removed for export] *)
    Lemma asn_pfd4 : forall mm iz' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 x28 x29 x30 x31,
      asn_frame mm -> iz' = iz ->
      evt asegs POST (STQ 0x4305c mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 (Z_to_bv 64 iz') x28 x29 x30 x31).
    Proof.
      intros until x31. intros AF ->. pose proof Hir as HIR. pose proof RP as RB.
      pose proof AF as AF'. asn_intro AF'. icpt_split IC'.
      zstep. if_cases K1; zify_cond K1.
      - (* [comment removed for export] *)
        zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
        zstep. zstep. zstep. zstep. fold_lits. rewrite (zb_lxor_ones p) by lia. zstep. sh_if_true.
        apply asn_p0f4; [exact AF| lia| reflexivity].
      - do 3 zstep. fold_lits. zstep. zstep. fold_lits. zstep. sh_if_true.
        zstep. zstep. if_cases K3; zify_cond K3.
        + zstep. zstep. zstep. zstep. fold_lits. rewrite (zb_lxor_ones p) by lia. zstep. sh_if_true.
          apply asn_p0f4; [exact AF| lia| reflexivity].
        + zstep. zstep. zstep. fold_lits. rewrite (zb_lxor_ones p) by lia. zstep. sh_if_false.
          apply asn_p0f4; [exact AF| lia| reflexivity].
    Qed.
  End QPhase.


  (* [comment removed for export] *)
  Lemma asn_loop : forall mm (k : nat) (j : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    asn_frame mm -> 0 < n ->
    Z.to_nat (n - j) = k -> 0 <= j < n -> j <= iz ->
    (forall kk, (kk < Z.to_nat j)%nat -> exists c, nth_error (map bv_unsigned x) kk = Some c /\ nth_error (map bv_unsigned y) kk = Some c /\ c <> 0) ->
    evt asegs POST (ST_ 0x43034 mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 j) x28 x29 x30 x31).
  Proof.
    intros mm k. induction k as [|k IH]; intros j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 AF N0 Hk Hj Hji HP;
      pose proof Hir as HIR; pose proof RP as RBP; pose proof RQ as RBQ; [lia|].
    pose proof AF as AF'. asn_intro AF'.
    assert (Hjr : j < r) by lia.
    (* [comment removed for export] *)
    destruct (nth_error x (Z.to_nat j)) as [bx|] eqn:EX. 2:{ exfalso. apply nth_error_None in EX. lia. }
    destruct (nth_error y (Z.to_nat j)) as [by_|] eqn:EY. 2:{ exfalso. apply nth_error_None in EY. lia. }
    pose proof (u8ro_read asegs mm p x j bx _ X' EX ltac:(lia) eq_refl) as RDX.
    pose proof (u8ro_read asegs mm q y j by_ _ Y' EY ltac:(lia) eq_refl) as RDY.
    pose proof (bv_unsigned_in_range 8 bx) as RBX. pose proof (bv_unsigned_in_range 8 by_) as RBY. unfold bv_modulus in RBX, RBY. cbn in RBX, RBY.
    assert (MX : nth_error (map bv_unsigned x) (Z.to_nat j) = Some (bv_unsigned bx)) by (rewrite nth_error_map, EX; reflexivity).
    assert (MY : nth_error (map bv_unsigned y) (Z.to_nat j) = Some (bv_unsigned by_)) by (rewrite nth_error_map, EY; reflexivity).
    zstep. zstep. zstep. zstep.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      destruct (strncmp_facts_stop _ _ (Z.to_nat n) (Z.to_nat j) _ _ ltac:(lia) MX MY HP ltac:(left; exact K1)) as [E1 E2].
      assert (Ej : j = iz) by (rewrite Hiz, E1; lia). subst j.
      eapply (asn_pfd4 (bv_unsigned bx) (bv_unsigned by_)); [lia| lia| exact E2| exact AF| reflexivity].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        destruct (strncmp_facts_stop _ _ (Z.to_nat n) (Z.to_nat j) _ _ ltac:(lia) MX MY HP ltac:(right; exact K2)) as [E1 E2].
        assert (Ej : j = iz) by (rewrite Hiz, E1; lia). subst j.
        eapply (asn_pfd4 (bv_unsigned bx) (bv_unsigned by_)); [lia| lia| exact E2| exact AF| reflexivity].
      + (* [comment removed for export] *)
        assert (HP' : forall kk, (kk < Z.to_nat (j + 1))%nat ->
                  exists c, nth_error (map bv_unsigned x) kk = Some c /\ nth_error (map bv_unsigned y) kk = Some c /\ c <> 0).
        { intros kk Hkk. destruct (Nat.eq_dec kk (Z.to_nat j)) as [->|NE].
          - exists (bv_unsigned bx). rewrite MX, MY. repeat split; [f_equal; lia| lia].
          - apply HP. lia. }
        zstep. zstep. if_cases K3; zify_cond K3.
        * (* [comment removed for export] *)
          assert (Hji' : j + 1 <= iz).
          { rewrite Hiz. pose proof (strncmp_stop_ge (map bv_unsigned x) (map bv_unsigned y) (Z.to_nat n) (Z.to_nat (j + 1)) HP' ltac:(lia)). lia. }
          apply (IH (j + 1)); try assumption; lia.
        * (* [comment removed for export] *)
          destruct (strncmp_facts_all (map bv_unsigned x) (map bv_unsigned y) (Z.to_nat n)) as [E1 E2].
          { intros kk Hkk. apply HP'. lia. }
          zstep. zstep.
          assert (En : n = iz) by (rewrite Hiz, E1; lia).
          eapply (asn_pfd4 (bv_unsigned bx) (bv_unsigned bx)); [lia| lia| rewrite E2, Z.eqb_refl; reflexivity| exact AF| exact En].
  Qed.

  (* [comment removed for export] *)
  Lemma asn_body : forall mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    asn_frame mm ->
    evt asegs POST (ST_ 0x4301c mm rae x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof Hir as HIR. pose proof RP as RBP. pose proof RQ as RBQ.
    pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof AF as AF'. asn_intro AF'. pose proof IC' as IC2. pose proof SOP as SOP2. pose proof SOQ as SOQ2.
    zstep. call asan_inited_ok; [exact IC'| exact MI'|].
    zstep. sh_if_false.
    pose proof (munch_refl [(bv_unsigned sp - 2176 - 16, bv_unsigned sp - 2176)] mm) as MU1.
    zstep. callsp try_init_ok; [exact IC'| exact MI'| exact ST'| exact CEIL| lia|].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
        (nelim (asn_after_callee mm mm2 16 IC2 SOP2 SOQ2 ltac:(lia) MUc) 3%nat; intros IC3 SOP3 SOQ3); clear MUc
      end end.
    zstep. sh_if_false.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      do 6 zstep. fold_lits. sh_if_true.
      do 4 zstep. fold_lits. rewrite (zb_lxor_ones p) by lia. zstep. sh_if_true.
      assert (X0 : x = []) by (destruct x; [reflexivity| cbn in LX; lia]).
      assert (Y0 : y = []) by (destruct y; [reflexivity| cbn in LY; lia]).
      assert (IZ0 : iz = 0) by (rewrite Hiz, X0, Y0; replace (Z.to_nat n) with 0%nat by lia; reflexivity).
      eapply (asn_p0f4 0 0); [lia| lia| rewrite X0, Y0; replace (Z.to_nat n) with 0%nat by lia; reflexivity| | lia| lia].
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); assumption.
    - zstep.
      eapply (asn_loop _ (Z.to_nat (n - 0)) 0); try lia.
      all: try (intros kk Hkk; exfalso; lia).
      all: refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); assumption.
  Qed.
End StrncmpIcpt.

Lemma strncmp_icpt_ok : strncmp_icpt_spec.
Proof.
  unfold strncmp_icpt_spec.
  intros until lo. intros IC MI ST CEIL SPB -> -> -> HN LX LY X Y ARP ARQ ASO SEPP SEPQ.
  set (i := strncmp_stop (map bv_unsigned x) (map bv_unsigned y) (Z.to_nat n)) in *.
  set (r := Z.min (Z.of_nat i + 1) n) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  assert (SE : ASTRFN_STACK = 2400) by reflexivity.
  pose proof (app_range_lt47 _ _ ARP) as RBP. pose proof (app_range_lt47 _ _ ARQ) as RBQ.
  assert (HR : 0 <= r <= n) by (pose proof (strncmp_stop_le (map bv_unsigned x) (map bv_unsigned y) (Z.to_nat n)); subst r i; lia).
  pose proof (munch_refl [(bv_unsigned sp - ASTRFN_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (conj IC (conj ASO (conj X Y))) as PK.
  unfold ASTRNCMP_T.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 104%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  sepM. do 16 zstep. do 4 zstep.
  (nelim PK 4%nat; intros IC0 ASO0 X0 Y0). clear IC ASO.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
  assert (IC1 : icpt_cells m0);
  [ eapply icpt_cells_munch; [exact IC0| exact MU|]; unfold icpt_cell_ivs;
    repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil |];
  assert (SOP1 : 0 < n -> shadow_ok m0 p r);
  [ intros N0; pose proof (SH_bounds p ltac:(lia)) as B1; pose proof (SH_bounds (p + r - 1) ltac:(lia)) as B2;
    eapply shadow_ok_munch; [exact (proj1 (ASO0 N0))| exact MU| subst r; lia| lia| lia|]; cbn; lia |];
  assert (SOQ1 : 0 < n -> shadow_ok m0 q r);
  [ intros N0; pose proof (SH_bounds q ltac:(lia)) as B1; pose proof (SH_bounds (q + r - 1) ltac:(lia)) as B2;
    eapply shadow_ok_munch; [exact (proj2 (ASO0 N0))| exact MU| subst r; lia| lia| lia|]; cbn; lia |];
  assert (X1 : bytes_at asegs m0 p x);
  [ eapply bytes_at_transport; [exact X0| exact MU|]; cbn; lia |];
  assert (Y1 : bytes_at asegs m0 q y);
  [ eapply bytes_at_transport; [exact Y0| exact MU|]; cbn; lia |];
  destruct (stk_split asegs m0 lo (bv_unsigned sp + -2176) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 ST2]
  end.
  eapply (asn_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p q n lo x y (Z.of_nat i) r);
    try eassumption; try reflexivity; try lia.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); eassumption.
Qed.


End CeilWrap.
End ICPT_str2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow ICPT_iface RT_poison RT_poison2 F_memchr ICPT_mem.
Import ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S C N : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res S (C mod 256) N buf)) a1' a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' S buf.

Lemma memchr_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S C N : Z) (buf : list byte),
  bytes_at asegs m S buf -> memchr_ok S (C mod 256) N buf ->
  0 <= S < 2^64 -> 0 <= C < 2^64 -> 0 <= N < 2^64 -> mem_inv asegs m ->
  evt asegs (memchr_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S C N buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9b0f4) fc None m (seg_rom asegs)).
Proof.
  intros until buf. intros BA OK HS HC HN MI.
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memchr_spec; rewrite ?ES, ?EC, ?EN; [exact BA | exact OK | exact MI]. }
  intros ms' P. unfold memchr_post, memchr_postv in *. rewrite ES, EC, EN in P. exact P.
Qed.

Section MemchrIcpt.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (s c n lo : Z) (buf : list byte).
  Variables (R L : Z).
  Hypothesis HN : 0 <= n < 2^40.
  Hypothesis HC : 0 <= c < 2^64.
  Hypothesis HS : 0 <= s /\ s + Z.of_nat (length buf) < 2^47.
  Hypothesis OK : memchr_ok s (c mod 256) n buf.
  Hypothesis HR : R = memchr_res s (c mod 256) n buf.
  Hypothesis HL : L = memchr_chk_len s (c mod 256) n buf.
  Hypothesis ARL : 0 < L -> app_range s L.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + AINTRIN_STACK <= bv_unsigned sp.
  Hypothesis SEP : s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s.

  Lemma RL_facts : (R = 0 /\ L = n) \/ (exists i, (i < length buf)%nat /\ Z.of_nat i < n /\ R = s + Z.of_nat i /\ R <> 0 /\ L = Z.of_nat i + 1).
  Proof.
    subst R L. unfold memchr_chk_len, memchr_res.
    destruct (find_byte (c mod 256) (firstn (Z.to_nat n) buf)) as [i|] eqn:E.
    - pose proof (proj1 (find_byte_Some _ _ _ E)) as Hi. rewrite length_firstn in Hi.
      destruct (Z.eqb_spec (s + Z.of_nat i) 0).
      + left. lia.
      + right. exists i. repeat split; lia.
    - left. rewrite Z.eqb_refl. auto.
  Qed.
  Lemma L_bounds : 0 <= L <= Z.max n 1 /\ (0 < L -> 0 <= s /\ s + L < 2^47).
  Proof.
    split. { destruct RL_facts as [[_ ->]|(i & _ & Hi & _ & _ & ->)]; lia. }
    intros H. exact (app_range_lt47 _ _ (ARL H)).
  Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv : AINTRIN_STACK = 2304. Proof. reflexivity. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (memchr_icpt_post rae sp gp tp s0e s1e s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 F fc s c n buf lo m).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9
            x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 c) x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition imr_frame (mm : word -> option byte) : Prop :=
    mem_inv asegs mm /\ icpt_cells mm /\ stk asegs mm lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs mm (bv_unsigned sp + -56) [C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ bytes_at asegs mm s buf
    /\ munch [(bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)] m mm /\ wmono asegs m mm
    /\ stk asegs mm (bv_unsigned sp + -2128) (bv_unsigned sp + -56)
    /\ (0 < L -> shadow_ok mm s L).

  Ltac imr_intro AF := (nelim AF 9%nat; intros MI' IC' ST' FR' BUF' MU' WM' ST2 SO).
  Ltac imr_pack := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); assumption.

  Lemma imr_after_callee : forall mm mm' k,
    icpt_cells mm -> (0 < L -> shadow_ok mm s L) -> 0 <= k <= 80 ->
    munch [(bv_unsigned sp - 2128 - k, bv_unsigned sp - 2128)] mm mm' ->
    icpt_cells mm' /\ (0 < L -> shadow_ok mm' s L).
  Proof.
    intros mm mm' k IC SO Hk MUr. pose proof L_bounds as [LB1 LB2]. pose proof CEILv. pose proof STKv.
    split.
    - eapply icpt_cells_munch; [exact IC| exact MUr|]. unfold icpt_cell_ivs.
      repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - intros L0. destruct (LB2 L0) as [HS1 HS2].
      pose proof (SH_bounds s ltac:(lia)). pose proof (SH_bounds (s + L - 1) ltac:(lia)).
      eapply shadow_ok_munch; [exact (SO L0)| exact MUr| lia| lia| lia|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma imr_ret : forall mm x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31,
    imr_frame mm ->
    evt asegs POST (ST_ 0x44294 mm x1 x5 x6 x7 x9 (Z_to_bv 64 R) x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. imr_intro AF.
    pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with ST1 : stk asegs mm2 lo _ |- _ =>
      lazymatch goal with ST3 : stk asegs mm2 (bv_unsigned sp + -2128) _ |- _ =>
      lazymatch goal with FR3 : rw_cells asegs mm2 (bv_unsigned sp + -56) _ |- _ =>
        pose proof (stk_merge asegs mm2 _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end end end.
    subst R. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma imr_region : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
    imr_frame mm -> 0 < L ->
    evt asegs POST (ST_ 0x443bc mm x1 x5 x6 x7 (Z_to_bv 64 L) (Z_to_bv 64 R) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF L0. imr_intro AF.
    pose proof L_bounds as [LB1 LB2]. destruct (LB2 L0) as [HS1 HS2].
    pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof IC' as IC2. pose proof SO as SO2.
    pose proof (munch_refl [(bv_unsigned sp - 2128 - 80, bv_unsigned sp - 2128)] mm) as MU1.
    assert (RR : 0 <= R < 2^64) by (destruct RL_facts as [[-> _]|(i & A1 & A2 & -> & A4 & A5)]; lia).
    do 4 zstep.
    callsp region_is_poisoned_ok;
      [ exact IC' | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact (ARL L0) | exact (SO L0) | ].
    zstep. zstep. zstep. fold_lits. sh_if_true.
    apply imr_ret.
    lazymatch goal with |- imr_frame ?mm2 =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
        destruct (imr_after_callee mm mm2 80 IC2 SO2 ltac:(lia) MUc) as [IC3 SO3]
      end end.
    imr_pack.
  Qed.

  (* [comment removed for export] *)
  Lemma imr_6bc : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
    imr_frame mm ->
    evt asegs POST (ST_ 0x44380 mm x1 x5 x6 x7 (Z_to_bv 64 L) (Z_to_bv 64 R) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof L_bounds as [LB1 LB2].
    zstep. if_cases K; zify_cond K.
    - apply imr_region; [exact AF| lia].
    - zstep. apply imr_ret. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma imr_6f0 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
    imr_frame mm -> 0 < L ->
    evt asegs POST (ST_ 0x443b4 mm x1 x5 x6 x7 (Z_to_bv 64 L) (Z_to_bv 64 R) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF L0. pose proof L_bounds as [LB1 LB2].
    zstep. zstep. if_cases K.
    - apply imr_ret. exact AF.
    - apply imr_region; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma imr_loop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 (acc : word) x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
    imr_frame mm -> 0 < L ->
    Z.to_nat (SH (s + L - 1) - SH s - i) = k -> 0 <= i -> SH s + i < SH (s + L - 1) ->
    evt asegs POST (ST_ 0x443a4 mm x1 x5 x6 x7 (Z_to_bv 64 L) (Z_to_bv 64 R) (Z_to_bv 64 (2147450880 + s / 8 + i)) (Z_to_bv 64 (2147450880 + (s + L - 1) / 8))
                        acc x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x28 x29 x30 x31).
  Proof.
    intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 acc x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 AF L0 Hk Hi Hlt;
      pose proof L_bounds as [LB1 LB2]; destruct (LB2 L0) as [HS1 HS2];
      pose proof (SH_bounds s ltac:(lia)) as B1; pose proof (SH_bounds (s + L - 1) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    pose proof AF as AF'. imr_intro AF'.
    assert (V : exists b, mm (wa (2147450880 + s / 8 + i)) = Some b).
    { destruct (mm (wa (2147450880 + s / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 (SO L0) (2147450880 + s / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - replace (2147450880 + s / 8 + i + 1) with (2147450880 + s / 8 + (i + 1)) by lia.
      apply (IH (i + 1)); try assumption; lia.
    - replace (2147450880 + s / 8 + i + 1) with (2147450880 + (s + L - 1) / 8) by lia.
      apply imr_6f0; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma imr_slow : forall mm x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
    imr_frame mm -> 0 < L ->
    evt asegs POST (ST_ 0x44388 mm x1 x5 x6 x7 (Z_to_bv 64 L) (Z_to_bv 64 R) (Z_to_bv 64 (2147450880 + s / 8)) (Z_to_bv 64 (2147450880 + (s + L - 1) / 8))
                        (Z_to_bv 64 (s + L - 1)) x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF L0. pose proof L_bounds as [LB1 LB2]. destruct (LB2 L0) as [HS1 HS2].
    pose proof (SH_bounds s ltac:(lia)) as B1. pose proof (SH_bounds (s + L - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. imr_intro AF'.
    (nelim (shadow_ok_shb mm s L (L - 1) (SO L0) ltac:(lia)) 3%nat; intros ve SHE Ce).
    replace (s + (L - 1)) with (s + L - 1) in SHE, Ce by lia.
    pose proof (shb_load_div' mm (s + L - 1) ve (s + L - 1) SHE eq_refl ltac:(lia)) as RD.
    step. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases K; zify_cond K.
    - apply imr_6f0; assumption.
    - replace (2147450880 + s / 8) with (2147450880 + s / 8 + 0) by lia.
      eapply (imr_loop mm (Z.to_nat (SH (s + L - 1) - SH s - 0)) 0); try exact AF; try exact L0; unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma imr_quick : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
    imr_frame mm -> 0 < L <= 64 ->
    evt asegs POST (ST_ 0x44258 mm x1 x5 x6 x7 (Z_to_bv 64 L) (Z_to_bv 64 R) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF L64. pose proof L_bounds as [LB1 LB2]. destruct (LB2 ltac:(lia)) as [HS1 HS2].
    pose proof (SH_bounds s ltac:(lia)) as B1. pose proof (SH_bounds (s + L - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. imr_intro AF'.
    icpt_split IC'.
    do 9 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    replace (s + L + -1) with (s + L - 1) by lia.
    zstep. zstep. rewrite !land_m8 by lia.
    destruct (vis_read8 mm ((2147450880 + s / 8) / 8 * 8)) as (w1 & L1 & W1). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 (SO ltac:(lia))). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 mm ((2147450880 + (s + L - 1) / 8) / 8 * 8)) as (w2 & L2 & W2). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 (SO ltac:(lia))). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases K.
    - apply imr_slow; [exact AF| lia].
    - apply imr_ret. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma imr_588 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
    imr_frame mm ->
    evt asegs POST (ST_ 0x4424c mm x1 x5 x6 x7 (Z_to_bv 64 L) (Z_to_bv 64 R) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof L_bounds as [LB1 LB2].
    zstep. zstep. zstep. fold_lits.
    destruct (Z.eq_dec L 0) as [Z0|Z0].
    { sh_if_true. apply imr_6bc. exact AF. }
    destruct (Z.lt_ge_cases 64 L) as [L64|L64].
    { sh_if_true. apply imr_6bc. exact AF. }
    sh_if_false. apply imr_quick; [exact AF| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma imr_body : forall mm x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
    imr_frame mm ->
    evt asegs POST (ST_ 0x4420c mm rae x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 s) (Z_to_bv 64 c) (Z_to_bv 64 n) x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof L_bounds as [LB1 LB2].
    pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof AF as AF'. imr_intro AF'. pose proof IC' as IC2. pose proof SO as SO2.
    zstep. call asan_inited_ok; [exact IC'| exact MI'|].
    zstep. sh_if_false.
    pose proof (munch_refl [(bv_unsigned sp - 2128 - 16, bv_unsigned sp - 2128)] mm) as MU1.
    zstep. callsp try_init_ok; [exact IC'| exact MI'| exact ST'| exact CEIL| lia|].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
        destruct (imr_after_callee mm mm2 16 IC2 SO2 ltac:(lia) MUc) as [IC3 SO3]; clear MUc
      end end.
    pose proof IC3 as IC4. icpt_split IC4.
    do 7 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) => pose proof (munch_refl [] mm2) as MU0 end.
    call memchr_callv; [eassumption| exact OK| lia| lia| lia| eassumption|].
    lazymatch type of MU0 with munch [] ?mm2 ?mm3 =>
      assert (IC5 : icpt_cells mm3) by
        (eapply icpt_cells_munch; [exact IC3| exact MU0| apply Forall_forall; intros; exact I]);
      assert (SO5 : 0 < L -> shadow_ok mm3 s L) by
        (intros L0; destruct (LB2 L0) as [HS1 HS2];
         eapply shadow_ok_munch; [exact (SO3 L0)| exact MU0| lia| | | exact I];
         pose proof (SH_bounds s ltac:(lia)); pose proof (SH_bounds (s + L - 1) ltac:(lia)); lia)
    end.
    rewrite <- HR.
    zstep. fold_lits. sh_if_false.
    assert (RR : 0 <= R < 2^64) by (destruct RL_facts as [[-> _]|(i & A1 & A2 & -> & A4 & A5)]; lia).
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      destruct RL_facts as [[R0 _]|(i & A1 & A2 & ER & A4 & EL)]; [exfalso; lia|].
      do 5 zstep. fold_lits. rewrite (zb_lxor_ones s) by lia.
      zstep. sh_if_true.
      replace (R - s + 1) with L by lia. apply imr_588. imr_pack.
    - (* [comment removed for export] *)
      destruct RL_facts as [[R0 EL]|(i & A1 & A2 & ER & A4 & EL)]; [| exfalso; lia].
      do 3 zstep. fold_lits. rewrite (zb_lxor_ones s) by lia.
      zstep. sh_if_false.
      replace (Z_to_bv 64 n) with (Z_to_bv 64 L) by (f_equal; lia). apply imr_588. imr_pack.
  Qed.
End MemchrIcpt.

Lemma memchr_icpt_ok : memchr_icpt_spec.
Proof.
  unfold memchr_icpt_spec.
  intros until lo. intros IC MI ST CEIL SPB -> -> -> HC HN BUF OK ARB ASO SEP.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
  assert (SE : AINTRIN_STACK = 2304) by reflexivity.
  set (L := memchr_chk_len s (c mod 256) n buf) in *.
  pose proof (munch_refl [(bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (conj IC (conj ASO BUF)) as PK.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof (app_range_lt47 _ _ ARB) as HS.
  unfold AMEMCHR_T.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 56%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 13 zstep.
  (nelim PK 3%nat; intros IC0 ASO0 BUF0). clear IC ASO.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
  assert (IC1 : icpt_cells m0);
  [ eapply icpt_cells_munch; [exact IC0| exact MU|]; unfold icpt_cell_ivs;
    repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil |];
  assert (SO1 : 0 < L -> shadow_ok m0 s L);
  [ intros L0; destruct (ASO0 L0) as [AR SO0]; pose proof (app_range_lt47 _ _ AR) as RB;
    pose proof (SH_bounds s ltac:(lia)) as B1; pose proof (SH_bounds (s + L - 1) ltac:(lia)) as B2;
    eapply shadow_ok_munch; [exact SO0| exact MU| lia| lia| lia|]; cbn; lia |];
  assert (BUF1 : bytes_at asegs m0 s buf);
  [ eapply bytes_at_transport; [exact BUF0| exact MU|]; cbn; lia |];
  destruct (stk_split asegs m0 lo (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ST ltac:(lia)) as [ST1 ST2]
  end.
  eapply (imr_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s c n lo buf _ L);
    try eassumption; try reflexivity; try lia.
  { intros L0. exact (proj1 (ASO0 L0)). }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); eassumption.
Qed.



End CeilWrap.
