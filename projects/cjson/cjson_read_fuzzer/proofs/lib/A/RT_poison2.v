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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow ICPT_iface RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma stk_lo_nonneg' : forall segs m lo hi, stk segs m lo hi -> (0 <= lo)%Z.
Proof. intros segs m lo hi (H & _). exact H. Qed.

(* [comment removed for export] *)
Ltac name_sp' sp k :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
    by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
        try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg' _ _ _ _ ST) end;
        apply unsigned_lit; lia).
Ltac unname_sp' :=
  match goal with
  | H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
      constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
  end.
Tactic Notation "callsp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp' sp k; call SPEC; unname_sp'
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp' sp k; call SPEC; unname_sp'
  | _ => call SPEC
  end.

Section RegionIsPoisoned.
  (* [comment removed for export] *)
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (b n lo : Z) (junk : list byte).
  Variables (vb ve sb se : Z).
  Hypothesis HN : 0 < n < 2^40.
  Hypothesis AR : app_range b n.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + 80 <= bv_unsigned sp.
  (* [comment removed for export] *)
  Hypothesis MI : mem_inv asegs m1.
  Hypothesis IC : icpt_cells m1.
  Hypothesis ST : stk asegs m1 lo (bv_unsigned sp + -64).
  Hypothesis FR : rw_cells asegs m1 (bv_unsigned sp + -64)
                    [CB 8 junk; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae].
  Hypothesis MU : munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1.
  Hypothesis WM : wmono asegs m m1.
  (* [comment removed for export] *)
  Hypothesis SHB0 : shb m1 b vb.
  Hypothesis Cb : vb = 0 \/ (b mod 8 < vb /\ vb < 8).
  Hypothesis SHBE : shb m1 (b + n - 1) ve.
  Hypothesis Ce : ve = 0 \/ ((b + n - 1) mod 8 < ve /\ ve < 8).
  Hypothesis Hsb : sb = SH ((b + 7) / 8 * 8).
  Hypothesis Hse : se = SH ((b + n) / 8 * 8).
  Hypothesis ZMID : sb < se -> bytes_at asegs m1 sb (zeros (Z.to_nat (se - sb))).

  Lemma R47 : 0 <= b /\ b + n < 2^47.
  Proof. exact (app_range_lt47 b n AR). Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling.
  Proof. reflexivity. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (region_is_poisoned_post rae sp gp tp s0e s1e s2e s3e s4e s5e s6 s7 s8 s9 s10 s11 F fc lo m).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 b) (Z_to_bv 64 n)
            x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 0xaa278) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma rip_ret : forall mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    mem_inv asegs mm ->
    stk asegs mm lo (bv_unsigned sp + -64) ->
    rw_cells asegs mm (bv_unsigned sp + -64) [CB 8 junk; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m mm -> wmono asegs m mm ->
    evt asegs POST (ST_ 0x5617c mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros until x31. intros MI' ST' FR' MU' WM'.
    pose proof R47 as RB. pose proof (bv_unsigned_in_range 64 sp) as RSP. try pose proof CEILv as CEILlo.
    do 11 zstep.
    release_frame FR' ST' (bv_unsigned sp).
    finish.
  Qed.

  Lemma app_range_ru : addr_in_mem ((b + 7) / 8 * 8).
  Proof.
    destruct AR as [H|H]; [left|right]; unfold lowmem_range, highmem_range, KHIGHMEM_BEG, KHIGHMEM_END in *;
      Z.div_mod_to_equations; blia.
  Qed.
  Lemma app_range_rd : addr_in_mem ((b + n) / 8 * 8).
  Proof.
    destruct AR as [H|H]; [left|right]; unfold lowmem_range, highmem_range, KHIGHMEM_BEG, KHIGHMEM_END in *;
      Z.div_mod_to_equations; blia.
  Qed.

  Lemma sbse_bounds : 2147450880 <= sb /\ sb <= se + 1 /\ se < 0x10007fff8000 /\ se - sb <= n / 8 + 1.
  Proof. pose proof R47. subst sb se. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma rip_860 : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x56168 m1 x1 x5 x6 x7 (Z_to_bv 64 se) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 sb) x20 x28 x29 x30 x31).
  Proof.
    intros. pose proof R47 as RB. pose proof sbse_bounds as SB. pose proof (bv_unsigned_in_range 64 sp) as RSP. try pose proof CEILv as CEILlo.
    pose proof FR as FR'. pose proof ST as ST'. pose proof MU as MU'. pose proof WM as WM'. pose proof MI as MI'.
    zstep. if_cases K; zify_cond K.
    { eapply rip_ret; eassumption. }
    zstep. zstep. zstep.
    callsp mem_is_zero_ok;
      [ exact MI' | exact ST' | lia | reflexivity | reflexivity | lia
      | apply ZMID; lia | lia | lia | ].
    zstep. fold_lits. sh_if_false.
    eapply rip_ret; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rip_80c : forall x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x56114 m1 x1 x5 x6 x7 (Z_to_bv 64 se) (Z_to_bv 64 2147450880) x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 (b + n)) (Z_to_bv 64 sb) x20 x28 x29 x30 x31).
  Proof.
    intros. pose proof R47 as RB. pose proof sbse_bounds as SB.
    zstep. zstep. zstep.
    replace (b + n + -1) with (b + n - 1) by lia.
    pose proof (shb_load' m1 (b + n - 1) ve (b + n - 1) SHBE eq_refl ltac:(lia)) as SHR.
    step. clear SHR.
    destruct Ce as [-> | [C1 C2]].
    - step. sh_if_true. apply rip_860.
    - rewrite (sxb_zb_small ve) by lia. step. sh_if_false.
      zstep. step. sh_if_true. apply rip_860.
  Qed.

  (* [comment removed for export] *)
  Lemma rip_7f0 : forall x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x560f8 m1 x1 x5 x6 x7 (Z_to_bv 64 se) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 (b + n)) (Z_to_bv 64 sb) x20 x28 x29 x30 x31).
  Proof.
    intros. pose proof R47 as RB. pose proof sbse_bounds as SB.
    icpt_split IC.
    zstep. zstep. zstep.
    pose proof (shb_load' m1 b vb b SHB0 eq_refl ltac:(lia)) as SHR.
    step. clear SHR.
    destruct Cb as [-> | [C1 C2]].
    - step. sh_if_true. apply rip_80c.
    - rewrite (sxb_zb_small vb) by lia. step. sh_if_false.
      zstep. step. sh_if_false. apply rip_80c.
  Qed.

  (* [comment removed for export] *)
  Lemma rip_7d0 : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x560d8 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 (b + n)) x19 x20 x28 x29 x30 x31).
  Proof.
    intros. pose proof R47 as RB. pose proof sbse_bounds as SB. pose proof MI as MI'.
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. zstep. zstep. rewrite !land_m8 by lia.
    zstep.
    call memtoshadow_ok; [exact IC| exact MI'| reflexivity| apply app_range_ru|].
    zstep. zstep. zstep.
    call memtoshadow_ok; [exact IC| exact MI'| reflexivity| apply app_range_rd|].
    rewrite <- Hsb, <- Hse.
    apply rip_7f0.
  Qed.

  (* [comment removed for export] *)
  Lemma rip_788 : forall x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    evt asegs POST (ST_ 0x56090 m1 x1 x5 x6 x7 x10 (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879) x13 x14 x15 x16 x17
                        x18 x19 x20 x28 x29 x30 x31).
  Proof.
    intros. pose proof R47 as RB.
    icpt_split IC.
    zstep. replace (n + b) with (b + n) by lia. zstep.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *) apply rip_7d0.
    - destruct AR as [AR'|AR']; [exfalso; unfold lowmem_range in AR'; blia|].
      unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END in AR'.
      do 8 zstep. fold_lits. sh_if_true.
      do 6 zstep. fold_lits. sh_if_false.
      zstep. fold_lits. sh_if_false.
      apply rip_7d0.
  Qed.
End RegionIsPoisoned.

Lemma region_is_poisoned_ok : region_is_poisoned_spec.
Proof.
  unfold region_is_poisoned_spec. intros until lo. intros IC MI ST CEIL SPB -> -> HN AR SO.
  pose proof (app_range_lt47 b n AR) as RB.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (CEILv : alloc_ceiling = alloc_ceiling) by reflexivity. try pose proof CEILv as CEILlo.
  (* [comment removed for export] *)
  (nelim (shadow_ok_shb m b n 0 SO ltac:(lia)) 3%nat; intros vb SHB0 Cb). rewrite Z.add_0_r in SHB0, Cb.
  (nelim (shadow_ok_shb m b n (n - 1) SO ltac:(lia)) 3%nat; intros ve SHBE Ce).
  replace (b + (n - 1)) with (b + n - 1) in SHBE, Ce by lia.
  pose proof (shadow_ok_mid_zeros m b n SO ltac:(lia) ltac:(lia)) as ZM. cbn zeta in ZM.
  unfold AREGION_POISONED.
  carve_frame 64%nat ST.
  do 9 zstep.
  if_cases K0; zify_cond K0; [exfalso; lia|].
  zstep. zstep.
  (* [comment removed for export] *)
  assert (IC1 : icpt_cells m0).
  { eapply icpt_cells_munch; [exact IC| exact MU|]. unfold icpt_cell_ivs.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  assert (SB1 : shb m0 b vb).
  { eapply shb_munch_disjoint; [exact SHB0| exact MU| unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia| cbn; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia]. }
  assert (SE1 : shb m0 (b + n - 1) ve).
  { eapply shb_munch_disjoint; [exact SHBE| exact MU| unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia| cbn; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia]. }
  assert (ZM1 : SH ((b + 7) / 8 * 8) < SH ((b + n) / 8 * 8) ->
                bytes_at asegs m0 (SH ((b + 7) / 8 * 8)) (zeros (Z.to_nat (SH ((b + n) / 8 * 8) - SH ((b + 7) / 8 * 8))))).
  { intros Hlt. eapply bytes_at_transport; [apply ZM; lia| exact MU|].
    unfold zeros. rewrite repeat_length. cbn. unfold SH, SHADOW_OFFSET in *. Z.div_mod_to_equations. lia. }
  clear IC SHB0 SHBE ZM.
  replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) in MU by lia.
  pose proof IC1 as IC1'. icpt_split IC1'.
  do 8 zstep. fold_lits.
  if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    eapply rip_788; try eassumption; reflexivity.
  - destruct AR as [AR'|AR']; [exfalso; unfold lowmem_range in AR'; blia|].
    pose proof AR' as AR2. unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END in AR2.
    do 8 zstep. fold_lits. sh_if_true.
    do 6 zstep. fold_lits. sh_if_false.
    zstep. fold_lits. sh_if_false.
    eapply rip_788; try eassumption; try reflexivity. right; exact AR'.
Qed.



End CeilWrap.
(* [comment removed for export] *)
Ltac name_sp' sp k :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
    by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
        try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg' _ _ _ _ ST) end;
        apply unsigned_lit; lia).
Ltac unname_sp' :=
  match goal with
  | H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
      constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
  end.
Tactic Notation "callsp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp' sp k; call SPEC; unname_sp'
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp' sp k; call SPEC; unname_sp'
  | _ => call SPEC
  end.
