(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue Pj_steps.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Pj_mciA Pj_loc_akitA Pj_onceA.
From OssFuzzTheorems.simdjson.fuzz_dump.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Ltac canary_same := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; rewrite bv_eqb_Z, Z.eqb_refl; reflexivity)
  end; cbv_concl_iota.

Definition get_locale_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 384, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma get_locale_spec_0 : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 384)%Z -> (0x6cd000 <= lo)%Z ->
  ro_cells bsegs m 0x16ef68 [C8 (Z_to_bv 64 0x6cb3a8)] -> ro_cells bsegs m 0x6cb3a8 [C8 canary] -> mem_inv bsegs m ->
  evt bsegs (get_locale_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0x1d2a3) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x150b84) fc None m (seg_rom bsegs)).
Proof.
  intros until canary. intros ST LO LOLO GOT CAN MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 384%nat ST.
  do 22 lstep.
  if_false.
  do 2 lstep.
  if_true.
  do 5 lstep.
  if_true.
  do 6 lstep.
  if_false.
  do 3 lstep.
  if_false.
  do 3 lstep.
  if_false.
  do 3 lstep.
  if_true.
  lstep.
  if_false.
  do 3 lstep.
  if_true.
  do 4 lstep.
  canary_same.
  do 16 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold get_locale_post. sys_finish.
Qed.

Lemma get_locale_spec_n : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo cat : Z) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 384)%Z -> (0x6cd000 <= lo)%Z -> (1 <= cat <= 5)%Z ->
  ro_cells bsegs m 0x16ef68 [C8 (Z_to_bv 64 0x6cb3a8)] -> ro_cells bsegs m 0x6cb3a8 [C8 canary] -> mem_inv bsegs m ->
  evt bsegs (get_locale_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cat) (Z_to_bv 64 0x1d2a3) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x150b84) fc None m (seg_rom bsegs)).
Proof.
  intros until canary. intros ST LO LOLO CAT GOT CAN MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (CU : bv_unsigned (Z_to_bv 64 cat) = cat) by (apply unsigned_lit; lia).
  carve_frame 384%nat ST.
  do 22 lstep.
  if_false.
  do 2 lstep.
  if_true.
  do 5 lstep.
  if_true.
  do 6 lstep.
  if_false.
  do 3 lstep.
  if_false.
  do 3 lstep.
  if_false.
  do 3 lstep.
  if_true.
  lstep.
  if_true.
  do 4 lstep.
  canary_same.
  do 16 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold get_locale_post. sys_finish.
Qed.

Section AevtPieces.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Hypothesis MCI : memcmp_inner_icontract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Definition newlocale_postA (Σ : rts RT) (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x32e58) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) []%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ ART RT Σ m'
    /\ (stk bsegs m' lo (bv_unsigned sp)).

Lemma newlocale_aevt : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 496 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  ro_cells bsegs m 0x16ef68 [C8 (Z_to_bv 64 0x6cb3a8)] -> ro_cells bsegs m 0x6cb3a8 [C8 canary] ->
  ro_cells bsegs m 0x6cb5fb [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m 0x6cb6d8 [C4 (Z_to_bv 64 0)] -> mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', newlocale_postA Σ ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x7fffffff) (Z_to_bv 64 0x1d2a3) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1507f0) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros until canary. intros ST LO LOR SPT SPA HI GOT CAN NL LK MI ART0 HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 496, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  astart (bv_unsigned sp) (@nil (Z * Z))%Z.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 112%nat ST.
  do 20 lstep.
  if_true.
  do 3 lstep.
  if_true.
  lstep.
  if_false.
  do 3 lstep.
  lstep.
  call_sp get_locale_spec_0; [exact ST | lia | lia | exact GOT | exact CAN | assumption |].
  rename POST into ST.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_true.
  lstep.
  if_false.
  do 3 lstep.
  lstep.
  call_sp get_locale_spec_n; [exact ST | lia | lia | lia | exact GOT | exact CAN | assumption |].
  rename POST into ST.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_true.
  lstep.
  if_false.
  do 3 lstep.
  lstep.
  call_sp get_locale_spec_n; [exact ST | lia | lia | lia | exact GOT | exact CAN | assumption |].
  rename POST into ST.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_true.
  lstep.
  if_false.
  do 3 lstep.
  lstep.
  call_sp get_locale_spec_n; [exact ST | lia | lia | lia | exact GOT | exact CAN | assumption |].
  rename POST into ST.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_true.
  lstep.
  if_false.
  do 3 lstep.
  lstep.
  call_sp get_locale_spec_n; [exact ST | lia | lia | lia | exact GOT | exact CAN | assumption |].
  rename POST into ST.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_true.
  lstep.
  if_true.
  do 2 lstep.
  lstep.
  call_sp get_locale_spec_n; [exact ST | lia | lia | lia | exact GOT | exact CAN | assumption |].
  rename POST into ST.
  do 3 lstep.
  if_false.
  do 6 lstep.
  if_false.
  do 2 lstep.
  if_false.
  do 3 lstep.
  if_false.
  lstep.
  if_true.
  do 3 lstep.
  lstep.

  lazymatch type of FR with
  | rw_cells _ _ ?A (?c0 :: ?rest) => pose proof (proj1 (rw_cells_app bsegs _ A [c0] rest) FR) as [_ FRB]
  end.
  cbn [cells_size csize Nat.add] in FRB.
  lazymatch type of FRB with
  | rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      pose proof (proj1 (rw_cells_app bsegs _ A [c1; c2; c3; c4; c5; c6] rest) FRB) as [FRP _]
  end.
  destruct FRP as [[_ BP] _]. clear FRB.
  replace (bv_unsigned sp + -112 + Z.of_nat 8)%Z with (bv_unsigned sp + -104)%Z in BP by lia.
  lazymatch type of BP with
  | bytes_at _ ?mm _ ?bpv =>
      assert (BQ : bytes_at bsegs mm 0x32e58 (repeat (Z_to_bv 8 0) 48))
        by (apply ro_bytes_at; [assumption | lia | cbn; lia | apply (ro_bytes_b_sound bsegs); vm_compute; reflexivity]);
      acall (memcmpA_spec RT MCI PMc FDO MST Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (bv_unsigned sp + -104)%Z 0x32e58%Z bpv (repeat (Z_to_bv 8 0) 48) lo);
      [ reflexivity | reflexivity | reflexivity | reflexivity | a_nl | a_nl | a_nl | a_nl | cbn; lia | a_nl | exact BP | exact BQ
      | a_cks_stack | a_cks_lit (cloc_acc RT AF) | exact ARTX | assumption | a_call_ok
      | intros r R; apost_call ]
  end.
  rename PC into ST. clear POST.
  assert (R0 : r = Z_to_bv 64 0) by (apply R; vm_compute; reflexivity). subst r. clear R.
  lstep.
  if_true.
  do 5 lstep.
  if_false.
  do 4 lstep.
  canary_same.
  do 9 lstep.
  release_frame FR ST (bv_unsigned sp).
  afinish.
Qed.

End AevtPieces.
