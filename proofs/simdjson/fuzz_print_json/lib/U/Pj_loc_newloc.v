(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_steps.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import F_memcmp.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
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
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 384, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp).

Lemma get_locale_spec_0 : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 384)%Z -> (0x110000 <= lo)%Z ->
  rw_cells usegs m 0xdb8b0 [C8 (Z_to_bv 64 0x10ec58)] -> rw_cells usegs m 0x10ec58 [C8 canary] -> mem_inv usegs m ->
  evt usegs (get_locale_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0x12370) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc07c8) fc None m (seg_rom usegs)).
Proof.
  intros until canary. intros ST LO LOLO GOT CAN MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
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
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 384)%Z -> (0x110000 <= lo)%Z -> (1 <= cat <= 5)%Z ->
  rw_cells usegs m 0xdb8b0 [C8 (Z_to_bv 64 0x10ec58)] -> rw_cells usegs m 0x10ec58 [C8 canary] -> mem_inv usegs m ->
  evt usegs (get_locale_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cat) (Z_to_bv 64 0x12370) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc07c8) fc None m (seg_rom usegs)).
Proof.
  intros until canary. intros ST LO LOLO CAT GOT CAN MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
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

Definition newlocale_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x23cc8) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 496, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp).

Lemma newlocale_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 496)%Z -> (0x110000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells usegs m 0xdb8b0 [C8 (Z_to_bv 64 0x10ec58)] -> rw_cells usegs m 0x10ec58 [C8 canary] ->
  rw_cells usegs m 0x10ec7b [C1 (Z_to_bv 8 0)] -> rw_cells usegs m 0x10ed50 [C4 (Z_to_bv 64 0)] -> mem_inv usegs m ->
  evt usegs (newlocale_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x7fffffff) (Z_to_bv 64 0x12370) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc0434) fc None m (seg_rom usegs)).
Proof.
  intros until canary. intros ST LO LOLO HI GOT CAN NL LK MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 496, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
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
  | rw_cells _ _ ?A (?c0 :: ?rest) => pose proof (proj1 (rw_cells_app usegs _ A [c0] rest) FR) as [_ FRB]
  end.
  cbn [cells_size csize Nat.add] in FRB.
  lazymatch type of FRB with
  | rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      pose proof (proj1 (rw_cells_app usegs _ A [c1; c2; c3; c4; c5; c6] rest) FRB) as [FRP _]
  end.
  destruct FRP as [[_ BP] _]. clear FRB.
  replace (bv_unsigned sp + -112 + Z.of_nat 8)%Z with (bv_unsigned sp + -104)%Z in BP by lia.
  lazymatch type of BP with
  | bytes_at _ ?mm _ ?bpv =>
      assert (BQ : bytes_at usegs mm 0x23cc8 (repeat (Z_to_bv 8 0) 48))
        by (apply ro_bytes_at; [assumption | lia | cbn; lia | apply (ro_bytes_b_sound usegs); vm_compute; reflexivity]);
      eapply evt_cut;
      [ eapply memcmp_spec with (p := (bv_unsigned sp + -104)%Z) (q := 0x23cc8%Z) (bp := bpv) (bq := repeat (Z_to_bv 8 0) 48);
        [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | cbn; lia | cbn; lia | exact BP | exact BQ | assumption]
      | ]
  end.
  intros ms' (r & a1' & a2' & a3' & a4' & E & R). subst ms'.
  assert (R0 : r = Z_to_bv 64 0) by (apply R; vm_compute; reflexivity). subst r. clear R BP BQ.
  replace (ret_pc (Z_to_bv 64 0xc0658)) with (Z_to_bv 64 0xc0658) by (apply bv_eq; vm_compute; reflexivity).
  lstep.
  if_true.
  do 5 lstep.
  if_false.
  do 4 lstep.
  canary_same.
  do 9 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold newlocale_post. sys_finish.
Qed.
