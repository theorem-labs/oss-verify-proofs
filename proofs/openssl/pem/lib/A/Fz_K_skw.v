(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_env Fz_M_malloc Fz_M_realloc Fz_M_realloc_array Fz_T_sk Fz_ukit2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_skr_realloc : Z := 0x1fa808.     (* [comment removed for export] *)

Lemma SGS : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia. Qed.
Lemma SWR : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z. rewrite Z.mod_small by lia. lia. Qed.
Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).

(* [comment removed for export] *)
Lemma CB_join3 : forall (m : mem) D (a b : nat) j1 (v : word) j3,
  rw_cells asegs m D [CB a j1] -> rw_cells asegs m (D + Z.of_nat a) [C8 v] -> rw_cells asegs m (D + Z.of_nat a + 8) [CB b j3] ->
  rw_cells asegs m D [CB (a + 8 + b)%nat (j1 ++ cbytes (C8 v) ++ j3)].
Proof.
  intros m D a b j1 v j3 FRONT WORD BACK.
  pose proof (StrFun.rw_cells_CB_length _ _ _ _ _ FRONT) as LEN_FRONT.
  pose proof (StrFun.rw_cells_CB_length _ _ _ _ _ BACK) as LEN_BACK.
  assert (TAIL2 : rw_cells asegs m (D + Z.of_nat a) [C8 v; CB b j3]).
  { apply (proj2 (rw_cells_app m (D + Z.of_nat a) [C8 v] [CB b j3])). split; [exact WORD | exact BACK]. }
  assert (ALL3 : rw_cells asegs m D ([CB a j1] ++ [C8 v; CB b j3])).
  { apply (proj2 (rw_cells_app m D [CB a j1] [C8 v; CB b j3])). split; [exact FRONT|].
    cbn [cells_size csize]. rewrite Nat.add_0_r. exact TAIL2. }
  cbn [app] in ALL3.
  refine (th_cells_congr asegs m D _ _ _ _ _ ALL3).
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - cbn [cells_size csize]. lia.
  - cbn [cells_wf cell_wf]. split; [| exact I]. rewrite !length_app, length_le8. lia.
Qed.

(* [comment removed for export] *)
Lemma skp_w0g : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A num : Z) (pad data srt nalloc comp cmpt freet copyt : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo -> 0 <= num < 2 ^ 31 ->
  rw_cells asegs m A (sk_cells (Z_to_bv 64 num) pad data srt nalloc comp cmpt freet copyt) -> acc asegs m A 56 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a4' : word) (m' : mem),
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) val (Z_to_bv 64 num) (Z_to_bv 64 (Z.shiftr A 3)) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_sk_insert) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' A (sk_cells (Z_to_bv 64 num) pad data srt nalloc comp cmpt freet copyt))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) val a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sk_push) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val F fc m lo A num pad data srt nalloc comp cmpt freet copyt
    ObjHigh ObjAlign ObjBelowLo NumRange ObjCells ObjPoison Pristine ShadowBase Stack LoHigh LoRoom SpTop Inv.
  assert (ObjNonNull : bv_eqb (Z_to_bv 64 A) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite (unsigned_lit A) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. pose proof (Z_to_bv_bv_unsigned sp) as SpBack.
  revert Stack LoRoom SpTop SpRange SpBack. generalize (bv_unsigned sp) as SP. intros SP Stack LoRoom SpTop SpRange SpBack. subst sp.
  change (bv_modulus 64) with (2 ^ 64) in SpRange.
  unfold sk_cells in ObjCells. unfold SHB, g_shadow_memory_dynamic_address in ShadowBase. unfold e_sk_push, e_sk_insert.
  pose proof (wmono_refl asegs m) as Grows. pose proof (munch_refl [(SP - 16, SP)] m) as Touched.
  assert (ShadowFp : sh_fp [(SP - 16, SP)]) by sh_fp_lia.
  assert (PristineFp : ut_fp [(SP - 16, SP)]) by ut_fp_lia.
  carve_frame 16%nat Stack.
  do 5 zstep. rewrite ObjNonNull. cbv iota.
  do 6 zstep. zstep. zsh. th_if_lit.
  do 5 zstep. rewrite (t_sx32_small num) by lia.
  assert (Unwound : stk asegs m1 lo SP).
  { pose proof (stk_release asegs m1 lo (SP + -16) [C8 s0; C8 ra] Stack FR ltac:(lia)) as Back.
    cbn [cells_size csize Nat.add] in Back. replace SP with (SP + -16 + Z.of_nat 16) by lia. exact Back. }
  apply evt_done. exists a4, m1. split; [reflexivity|].
  split; [exact Touched|]. split; [exact Grows|]. split; [exact Inv|]. split; [exact Unwound| exact ObjCells].
Qed.

(* [comment removed for export] *)
Lemma ski_w0g : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A num loc : Z) (pad data srt nalloc comp cmpt freet copyt : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo -> 0 <= num < 2 ^ 31 - 1 ->
  rw_cells asegs m A (sk_cells (Z_to_bv 64 num) pad data srt nalloc comp cmpt freet copyt) -> acc asegs m A 56 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (j : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_ski_reserve) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 1) z64 a3 a4 a5 a6 a7
                   (Z_to_bv 64 loc) s3 val s5 s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 e_sk_reserve) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (bv_unsigned sp + -112) [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk asegs m' lo (bv_unsigned sp + -112) /\ rw_cells asegs m' A (sk_cells (Z_to_bv 64 num) pad data srt nalloc comp cmpt freet copyt))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) val (Z_to_bv 64 loc) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sk_insert) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val F fc m lo A num loc pad data srt nalloc comp cmpt freet copyt
    ObjHigh ObjAlign ObjBelowLo NumRange ObjCells ObjPoison Pristine ShadowBase Stack LoHigh LoRoom SpTop Inv.
  assert (ObjNonNull : bv_eqb (Z_to_bv 64 A) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite (unsigned_lit A) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia. }
  assert (NumNotMax : bv_eqb (Z_to_bv 64 num) (Z_to_bv 64 2147483647) = false).
  { unfold bv_eqb. rewrite (unsigned_lit num) by lia. change (bv_unsigned (Z_to_bv 64 2147483647)) with 2147483647. apply Z.eqb_neq. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. pose proof (Z_to_bv_bv_unsigned sp) as SpBack.
  revert Stack LoRoom SpTop SpRange SpBack. generalize (bv_unsigned sp) as SP. intros SP Stack LoRoom SpTop SpRange SpBack. subst sp.
  change (bv_modulus 64) with (2 ^ 64) in SpRange.
  unfold sk_cells in ObjCells. unfold SHB, g_shadow_memory_dynamic_address in ShadowBase. unfold e_sk_insert, e_sk_reserve, SITE_ski_reserve.
  pose proof (wmono_refl asegs m) as Grows. pose proof (munch_refl [(SP - 112, SP)] m) as Touched.
  assert (ShadowFp : sh_fp [(SP - 112, SP)]) by sh_fp_lia.
  assert (PristineFp : ut_fp [(SP - 112, SP)]) by ut_fp_lia.
  carve_frame 112%nat Stack.
  do 16 zstep. rewrite ObjNonNull. cbv iota.
  do 3 zstep. do 6 zstep. zstep. zsh. th_if_lit.
  zstep. rewrite (t_sx32_small num) by lia. zstep. zstep.
  zstep. rewrite NumNotMax. change (negb false) with true. cbv iota.
  do 4 zstep.
  apply evt_done. eexists. exists m0. split; [reflexivity|].
  split; [exact Touched|]. split; [exact Grows|]. split; [exact Inv|]. split; [exact FR|]. split; [exact Stack| exact ObjCells].
Qed.

(* [comment removed for export] *)
Lemma skr_room : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A D num nalloc : Z) (pad srt cmpt freet copyt : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo ->
  rw_cells asegs m A (sk_cells (Z_to_bv 64 num) pad (Z_to_bv 64 D) srt (Z_to_bv 64 nalloc) z64 cmpt freet copyt) -> acc asegs m A 56 ->
  1 <= num -> num + 1 <= nalloc -> 4 <= nalloc < 2 ^ 20 -> D <> 0 -> 0 <= D < 2 ^ 64 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' A (sk_cells (Z_to_bv 64 num) pad (Z_to_bv 64 D) srt (Z_to_bv 64 nalloc) z64 cmpt freet copyt))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 1) z64 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sk_reserve) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A D num nalloc pad srt cmpt freet copyt
    ObjHigh ObjAlign ObjBelowLo ObjCells ObjPoison NumPos NumRoom NallocRange DataNonZero DataRange Pristine ShadowBase Stack LoHigh LoRoom SpTop Inv.
  assert (FlipLow : Z.lxor num 2147483647 = 2147483647 - num).
  { change 2147483647 with (Z.ones 31). rewrite <- Z.ldiff_ones_l_low.
    - symmetry. apply Z.sub_nocarry_ldiff. rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.div_small by lia. reflexivity.
    - lia.
    - apply (proj1 (Z.log2_lt_pow2 num 31 ltac:(lia))). lia. }
  assert (BelowLimit : bv_ltu (Z_to_bv 64 (Z.lxor num 2147483647)) (Z_to_bv 64 1) = false).
  { unfold bv_ltu. rewrite FlipLow, unsigned_lit by lia. change (bv_unsigned (Z_to_bv 64 1)) with 1. apply Z.ltb_ge. lia. }
  assert (DataNotNull : bv_eqb (Z_to_bv 64 D) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite (unsigned_lit D) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. exact DataNonZero. }
  pose proof (SGS (num + 1) ltac:(lia)) as SgnNext. pose proof (SGS nalloc ltac:(lia)) as SgnCap.
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. pose proof (Z_to_bv_bv_unsigned sp) as SpBack.
  revert Stack LoRoom SpTop SpRange SpBack. generalize (bv_unsigned sp) as SP. intros SP Stack LoRoom SpTop SpRange SpBack. subst sp.
  change (bv_modulus 64) with (2 ^ 64) in SpRange.
  unfold sk_cells in ObjCells. unfold SHB, g_shadow_memory_dynamic_address in ShadowBase. unfold e_sk_reserve.
  pose proof (wmono_refl asegs m) as Grows. pose proof (munch_refl [(SP - 80, SP)] m) as Touched.
  assert (ShadowFp : sh_fp [(SP - 80, SP)]) by sh_fp_lia.
  assert (PristineFp : ut_fp [(SP - 80, SP)]) by ut_fp_lia.
  carve_frame 80%nat Stack.
  do 11 zstep.
  do 7 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small num) by lia. do 4 zstep.
  rewrite BelowLimit. change (negb false) with true. cbv iota.
  zstep. rewrite (SWR (num + 1)) by lia. zstep.
  zstep. if_cases MinFour; zify_cond MinFour.
  2: zstep.
  all: do 5 zstep; th_if_lit.
  all: do 2 zstep; rewrite DataNotNull; cbv iota.
  all: do 5 zstep; th_if_lit.
  all: zstep; rewrite (t_sx32_small nalloc) by lia.
  all: zstep; th_if_lit.
  all: zstep; if_cases RoomOk; zify_cond RoomOk; [| exfalso; lia].
  all: do 12 zstep.
  all: assert (Unwound : stk asegs m0 lo SP);
    [ pose proof (stk_release asegs m0 lo (SP + -80) _ Stack FR ltac:(lia)) as Back;
      cbn [cells_size csize Nat.add] in Back; replace SP with (SP + -80 + Z.of_nat 80) by lia; exact Back |].
  all: apply evt_done; do 5 eexists; exists m0; split; [reflexivity|].
  all: split; [exact Touched|]; split; [exact Grows|]; split; [exact Inv|]; split; [exact Unwound| exact ObjCells].
Qed.
(* [comment removed for export] *)
Lemma ski_w1g : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A D num nalloc s01 : Z) (pad cmpt freet copyt : word) (j junk : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo ->
  rw_cells asegs m A (sk_cells (Z_to_bv 64 num) pad (Z_to_bv 64 D) (Z_to_bv 64 s01) (Z_to_bv 64 nalloc) z64 cmpt freet copyt) -> acc asegs m A 56 ->
  1 <= num -> num + 1 <= nalloc -> 4 <= nalloc < 2 ^ 20 -> (s01 = 0 \/ s01 = 1) ->
  0x10007fff8000 <= D -> D mod 8 = 0 -> D + 8 * nalloc <= lo -> rw_cells asegs m D [CB (Z.to_nat (8 * nalloc)) junk] -> acc asegs m D (8 * nalloc) ->
  (A + 56 <= D \/ D + 8 * nalloc <= A) ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -112) [CB 8 j; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -112) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' a2' a3' a4' : word) (junk' : list byte) (m' : mem),
       ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 (num + 1)) a1' a2' a3' a4' a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(A, A + 4); (A + 16, A + 20); (D, D + 8 * nalloc)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' A (sk_cells (Z_to_bv 64 (num + 1)) pad (Z_to_bv 64 D) z64 (Z_to_bv 64 nalloc) z64 cmpt freet copyt)
       /\ rw_cells asegs m' D [CB (Z.to_nat (8 * nalloc)) junk'])
   (MS (mkR (Z_to_bv 64 SITE_ski_reserve) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 num) s3 val s5 s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ski_reserve) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s9 s10 s11 t3 t4 t5 t6 val F fc m lo A D num nalloc s01 pad cmpt freet copyt j junk
    rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
    ObjHigh ObjAlign ObjBelowLo ObjCells ObjPoison NumPos NumRoom NallocRange SortedFlag
    ArrHigh ArrAlign ArrBelowLo ArrCells ArrPoison Apart Pristine ShadowBase Saved Stack LoHigh LoRoom SpTop Inv.
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. pose proof (Z_to_bv_bv_unsigned sp) as SpBack.
  revert Saved Stack LoRoom SpTop SpRange SpBack. generalize (bv_unsigned sp) as SP. intros SP Saved Stack LoRoom SpTop SpRange SpBack. subst sp.
  change (bv_modulus 64) with (2 ^ 64) in SpRange.
  apply (rw_cells_split_CB asegs m D [] _ junk [] [Z.to_nat (8 * num); 8%nat; (Z.to_nat (8 * nalloc) - Z.to_nat (8 * num) - 8)%nat]) in ArrCells;
    [| cbn [sum_nat]; lia].
  cbn [mk_CB_cells app] in ArrCells.
  apply (proj1 (rw_cells_app m D [_] _)) in ArrCells. destruct ArrCells as [ArrLead ArrRest].
  apply (proj1 (rw_cells_app m _ [_] _)) in ArrRest. destruct ArrRest as [ArrSlot ArrTrail].
  cbn [cells_size csize Nat.add] in ArrSlot, ArrTrail.
  replace (D + Z.of_nat (Z.to_nat (8 * num) + 0)) with (D + 8 * num) in ArrSlot, ArrTrail by lia.
  change (Z.of_nat 8) with 8 in ArrTrail.
  unfold sk_cells in ObjCells. unfold SHB, SITE_ski_reserve. unfold g_shadow_memory_dynamic_address in ShadowBase.
  pose proof (wmono_refl asegs m) as Grows. pose proof (munch_refl [(A, A + 4); (A + 16, A + 20); (D, D + 8 * nalloc)] m) as Touched.
  assert (ShadowFp : sh_fp [(A, A + 4); (A + 16, A + 20); (D, D + 8 * nalloc)]) by sh_fp_lia.
  pose proof (zb_lxor_pow2_small num 63 ltac:(lia) ltac:(lia)) as SignedNum. change (2 ^ 63) with 9223372036854775808 in SignedNum.
  assert (PastSign : (num + 9223372036854775808 <? 9223372036854775808) = false) by (apply Z.ltb_ge; lia).
  assert (Shift8 : num ≪ 3 = 8 * num) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (SGS num ltac:(lia)) as SgnNum.
  zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small num) by lia.
  zstep. do 5 zstep.
  rewrite SignedNum, Z.ltb_irrefl, PastSign. th_if_lit.
  do 2 zstep. rewrite Shift8.
  remember (D + 8 * num) as Slot eqn:SlotAt.
  do 3 zstep. zstep. th_if_lit.
  zstep.
  do 2 zstep. zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small num) by lia.
  do 3 zstep.
  zstep.
  do 2 zstep. zstep. th_if_lit.
  zstep. destruct SortedFlag as [-> | ->]; rewrite t_sx32_small by lia.
  all: zstep; th_if_lit.
  2: zstep; if_cases HasMany; zify_cond HasMany; [exfalso; lia |].
  2: do 4 zstep; zstep; th_if_lit.
  2: do 2 zstep; th_if_lit.
  2: do 2 zstep; th_if_lit.
  2: zstep.
  all: zstep; zstep; th_if_lit.
  all: zstep; rewrite (t_sx32_small (num + 1)) by lia.
  all: do 15 zstep.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
         pose proof (stk_release asegs mf lo (SP + -112) _ Stack Saved ltac:(lia)) as Back;
         rename mf into mfin end.
  all: cbn [cells_size csize Nat.add] in Back; replace (SP + -112 + Z.of_nat 112) with SP in Back by lia.
  all: subst Slot.
  all: rewrite <- (Z2Nat.id (8 * num)) in ArrSlot, ArrTrail at 1 by lia.
  all: pose proof (CB_join3 mfin D _ _ _ val _ ArrLead ArrSlot ArrTrail) as Whole.
  all: replace (Z.to_nat (8 * num) + 8 + (Z.to_nat (8 * nalloc) - Z.to_nat (8 * num) - 8))%nat with (Z.to_nat (8 * nalloc)) in Whole by lia.
  all: apply evt_done; do 5 eexists; exists mfin; split; [reflexivity|].
  all: split; [exact Touched|]; split; [exact Grows|]; split; [exact Inv|]; split; [exact Back|]; split; [exact ObjCells| exact Whole].
Qed.
(* [comment removed for export] *)
Lemma skr_grow_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A D : Z) (pad srt cmpt freet copyt : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo ->
  rw_cells asegs m A (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 D) srt (Z_to_bv 64 4) z64 cmpt freet copyt) -> acc asegs m A 56 -> D <> 0 -> 0 <= D < 2 ^ 64 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (j : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_skr_realloc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 A)
                   (Z_to_bv 64 D) (Z_to_bv 64 6) (Z_to_bv 64 8) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 212) (Z_to_bv 64 6) a6 a7
                   (Z_to_bv 64 (A + 8)) (Z_to_bv 64 5) (Z_to_bv 64 (A + 20)) (Z_to_bv 64 (Z.shiftr (A + 8) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (A + 20) 3 + SHB)) (Z_to_bv 64 6)
                    s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_CRYPTO_realloc_array) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ stk asegs m' lo (bv_unsigned sp + -80) /\ rw_cells asegs m' A (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 D) srt (Z_to_bv 64 4) z64 cmpt freet copyt))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 1) z64 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sk_reserve) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A D pad srt cmpt freet copyt
    ObjHigh ObjAlign ObjBelowLo ObjCells ObjPoison DataNonZero DataRange Pristine ShadowBase Stack LoHigh LoRoom SpTop Inv.
  assert (DataNotNull : bv_eqb (Z_to_bv 64 D) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite (unsigned_lit D) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. exact DataNonZero. }
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. pose proof (Z_to_bv_bv_unsigned sp) as SpBack.
  revert Stack LoRoom SpTop SpRange SpBack. generalize (bv_unsigned sp) as SP. intros SP Stack LoRoom SpTop SpRange SpBack. subst sp.
  change (bv_modulus 64) with (2 ^ 64) in SpRange.
  unfold sk_cells in ObjCells. unfold SHB, g_shadow_memory_dynamic_address in ShadowBase. unfold e_sk_reserve.
  pose proof (wmono_refl asegs m) as Grows. pose proof (munch_refl [(SP - 80, SP)] m) as Touched.
  assert (ShadowFp : sh_fp [(SP - 80, SP)]) by sh_fp_lia.
  assert (PristineFp : ut_fp [(SP - 80, SP)]) by ut_fp_lia.
  carve_frame 80%nat Stack.
  do 11 zstep.
  do 7 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small 4) by lia. do 4 zstep. th_if_lit.
  do 3 zstep. th_if_lit.
  do 5 zstep. th_if_lit.
  do 2 zstep. rewrite DataNotNull. cbv iota.
  do 5 zstep. th_if_lit.
  zstep. rewrite (t_sx32_small 4) by lia.
  zstep. th_if_lit.
  zstep. th_if_lit.
  do 10 zstep. th_if_lit.
  do 7 zstep. th_if_lit.
  do 6 zstep.
  apply evt_done. eexists. exists m0. split; [reflexivity|].
  split; [exact Touched|]. split; [exact Grows|]. split; [exact Inv|]. split; [exact FR|]. split; [exact Stack| exact ObjCells].
Qed.

(* [comment removed for export] *)
Lemma skr_grow_w1 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A D q : Z) (pad srt cmpt freet copyt : word) (j : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo -> rw_cells asegs m A (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 D) srt (Z_to_bv 64 4) z64 cmpt freet copyt) -> acc asegs m A 56 ->
  0 < q < 2 ^ 64 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -80) [CB 8 j; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -80) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' : word) (m' : mem),
       ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(A + 8, A + 16); (A + 20, A + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' A (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 q) srt (Z_to_bv 64 6) z64 cmpt freet copyt))
    (MS (mkR (Z_to_bv 64 SITE_skr_realloc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 (A + 8)) (Z_to_bv 64 5) (Z_to_bv 64 (A + 20)) (Z_to_bv 64 (Z.shiftr (A + 8) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (A + 20) 3 + SHB)) (Z_to_bv 64 6)
            s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_skr_realloc) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A D q pad srt cmpt freet copyt j rav s0v s1v s2v s3v s4v s5v s6v s7v
    ObjHigh ObjAlign ObjBelowLo ObjCells ObjPoison NewRange Pristine ShadowBase Saved Stack LoHigh LoRoom SpTop Inv.
  assert (NewNotNull : bv_eqb (Z_to_bv 64 q) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite (unsigned_lit q) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. pose proof (Z_to_bv_bv_unsigned sp) as SpBack.
  revert Saved Stack LoRoom SpTop SpRange SpBack. generalize (bv_unsigned sp) as SP. intros SP Saved Stack LoRoom SpTop SpRange SpBack. subst sp.
  change (bv_modulus 64) with (2 ^ 64) in SpRange.
  unfold sk_cells in ObjCells. unfold SITE_skr_realloc, SHB. unfold g_shadow_memory_dynamic_address in ShadowBase.
  pose proof (wmono_refl asegs m) as Grows. pose proof (munch_refl [(A + 8, A + 16); (A + 20, A + 24)] m) as Touched.
  assert (ShadowFp : sh_fp [(A + 8, A + 16); (A + 20, A + 24)]) by sh_fp_lia.
  zstep. rewrite NewNotNull. cbv iota.
  zstep. zstep. th_if_lit.
  zstep.
  zstep. zstep. th_if_lit.
  zstep.
  do 12 zstep.
  assert (Unwound : stk asegs m1 lo SP).
  { pose proof (stk_release asegs m1 lo (SP + -80) _ Stack Saved ltac:(lia)) as Back.
    cbn [cells_size csize Nat.add] in Back. replace SP with (SP + -80 + Z.of_nat 80) by lia. exact Back. }
  apply evt_done. eexists. exists m1. split; [reflexivity|].
  split; [exact Touched|]. split; [exact Grows|]. split; [exact Inv|]. split; [exact Unwound| exact ObjCells].
Qed.
