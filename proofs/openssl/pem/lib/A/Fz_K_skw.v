(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
  intros m D a b j1 v j3 H1 H2 H3.
  pose proof (proj1 (proj1 H1)) as W1. pose proof (proj1 (proj1 H3)) as W3. cbn in W1, W3. destruct W1 as [W1 _]. destruct W3 as [W3 _].
  assert (H : rw_cells asegs m D ([CB a j1] ++ [C8 v] ++ [CB b j3])).
  { apply rw_cells_app. split; [exact H1|]. apply rw_cells_app. cbn [cells_size csize Nat.add].
    split; [replace (D + Z.of_nat (a + 0)) with (D + Z.of_nat a) by lia; exact H2|].
    replace (D + Z.of_nat (a + 0) + Z.of_nat 8) with (D + Z.of_nat a + 8) by lia. exact H3. }
  cbn [app] in H. eapply rw_cells_recast; [exact H| |].
  - cbn. rewrite !length_app. cbn. repeat split; try exact I. rewrite W1, W3. lia.
  - cbn. rewrite !app_nil_r. reflexivity.
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
  intros until copyt. intros AHI AAL ALO NUM HC ACC UT SHC ST LO0 LO HTOP MI. unfold e_sk_push, e_sk_insert, sk_cells, g_shadow_memory_dynamic_address, SHB in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 3 zstep. do 2 zstep. zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small num) by lia.
  do 2 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  finish.
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
  intros until copyt. intros AHI AAL ALO NUM HC ACC UT SHC ST LO0 LO HTOP MI. unfold e_sk_insert, e_sk_reserve, sk_cells, g_shadow_memory_dynamic_address, SHB, SITE_ski_reserve in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 112%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 15 zstep.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zstep.                                                    (* [comment removed for export] *)
  do 2 zstep. do 3 zstep. do 2 zstep. zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small num) by lia. do 2 zstep.
  zstep. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  do 3 zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; assumption.
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
  intros until copyt. intros AHI AAL ALO HC ACC NUM NA NAL D0 DR UT SHC ST LO0 LO HTOP MI.
  unfold e_sk_reserve, sk_cells, g_shadow_memory_dynamic_address, SHB in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 11 zstep.
  do 3 zstep.                                                             (* [comment removed for export] *)
  do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small num) by lia.
  (* [comment removed for export] *)
  do 3 zstep. zstep. rewrite ?Z.add_0_r, ?ubs_sw32 by lia.
  assert (XL : Z.lxor num 2147483647 = 2147483647 - num).
  { change 2147483647 with (Z.ones 31).
    assert (LL : Z.log2 num < 31) by (destruct (Z.eq_dec num 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
    rewrite <- Z.ldiff_ones_l_low; [| lia | exact LL]. symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; [lia | exact LL]. }
  if_cases K2; zify_cond K2; [| exfalso; rewrite ?SGS, ?unsigned_lit, ?ubs_sw32, ?XL in K2 by lia; clear - K2 NUM NA NAL; lia]. clear K2.
  (* [comment removed for export] *)
  zstep. rewrite ?ubs_sw32 by lia.
  zstep. zstep.
  if_cases K4; zify_cond K4; rewrite ?SGS, ?unsigned_lit in K4 by lia; [| zstep].
  all: do 4 zstep; zstep; th_if_lit; zstep.
  all: zstep; if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; exact (D0 K5)|].
  all: do 4 zstep; zstep; th_if_lit; zstep; rewrite (t_sx32_small nalloc) by lia.
  all: zstep; th_if_lit.
  all: zstep; if_cases K6; zify_cond K6; rewrite ?SGS, ?unsigned_lit in K6 by lia; [| exfalso; clear - K6 K4 NA NAL NUM; lia].
  all: zstep; do 9 zstep.
  all: th_release FR (bv_unsigned sp); do 2 zstep.
  all: apply evt_done; do 6 eexists; split; [cbv delta [mkR]; reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; assumption.
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
  intros until s11v. intros AHI AAL ALO HC ACC NUM NA NAL S01 DHI DAL DLO DC ACCD DISJ UT SHC FR ST LO0 LO HTOP MI.
  unfold sk_cells, g_shadow_memory_dynamic_address, SHB, SITE_ski_reserve in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 val) as RV. unfold bv_modulus in RV. cbn in RV.
  pose proof (munch_refl [(A, A + 4); (A + 16, A + 20); (D, D + 8 * nalloc)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-112) EU1.
  pose proof (proj1 (proj1 (proj1 DC))) as JL. cbn in JL.
  zstep. th_if_lit.
  zstep. zsh. zstep. th_if_lit.
  do 3 zstep. zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small num) by lia. zstep.
  do 4 zstep.
  change 9223372036854775808 with (2 ^ 63). rewrite !zb_lxor_sign by lia. rewrite (Z.mod_small (num + 2 ^ 63)) by lia.
  replace (num + 2 ^ 63 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Z.ltb_irrefl. cbn [Z.b2z Z.lxor Z.lor].
  zstep. th_if_lit.
  (* [comment removed for export] *)
  zstep. zstep. rewrite (Z.shiftl_mul_pow2 num 3) by lia. change (2 ^ 3) with 8.
  remember (D + num * 8) as cb eqn:ECB.
  assert (ACB : acc asegs m cb 8) by (apply (acc_sub asegs m D (8 * nalloc) cb 8 ACCD); subst cb; lia).
  assert (CBAL : cb mod 8 = 0) by (subst cb; clear - DAL; Z.div_mod_to_equations; lia).
  apply (rw_cells_split_CB asegs m D [] (Z.to_nat (8 * nalloc)) junk [] [Z.to_nat (8 * num); 8; Z.to_nat (8 * nalloc - 8 * num - 8)]%nat) in DC; [| cbn [sum_nat]; lia]. cbn [mk_CB_cells app] in DC.
  lazymatch type of DC with rw_cells _ _ _ [?c1; ?c2; ?c3] => change [c1; c2; c3] with ([c1] ++ [c2] ++ [c3]) in DC end.
  apply (proj1 (rw_cells_app m _ _ _)) in DC. destruct DC as [D1 DCr]. apply (proj1 (rw_cells_app m _ _ _)) in DCr. destruct DCr as [D2 D3].
  cbn [cells_size csize Nat.add] in D2, D3.
  replace (D + Z.of_nat (Z.to_nat (8 * num) + 0)) with cb in D2 by lia. replace (D + Z.of_nat (Z.to_nat (8 * num) + 0) + Z.of_nat 8) with (cb + 8) in D3 by lia.
  (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit.
  zstep.
  zstep. zstep.
  (* [comment removed for export] *)
  zstep. zsh. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small num) by lia.
  rewrite ?(SWR (num + 1)) by lia.
  do 5 zstep. zstep. zsh. zstep. try th_if_lit.
  zstep. rewrite (t_sx32_small s01) by lia.
  assert (JOIN : forall mx, rw_cells asegs mx D [CB (Z.to_nat (8 * num)) (firstn (Z.to_nat (8 * num)) junk)] -> rw_cells asegs mx cb [C8 val] ->
                  rw_cells asegs mx (cb + 8) [CB (Z.to_nat (8 * nalloc - 8 * num - 8)) (firstn (Z.to_nat (8 * nalloc - 8 * num - 8)) (skipn 8 (skipn (Z.to_nat (8 * num)) junk)))] ->
                  exists junk', rw_cells asegs mx D [CB (Z.to_nat (8 * nalloc)) junk']).
  { intros mx X1 X2 X3. eexists.
    replace (Z.to_nat (8 * nalloc)) with (Z.to_nat (8 * num) + 8 + Z.to_nat (8 * nalloc - 8 * num - 8))%nat by lia.
    eapply (CB_join3 mx D _ _ _ val _ X1); [rewrite Z2Nat.id by lia; replace (D + 8 * num) with cb by lia; exact X2|].
    rewrite Z2Nat.id by lia. replace (D + 8 * num + 8) with (cb + 8) by lia. exact X3. }
  destruct S01 as [-> | ->].
  - zstep. th_if_lit.
    zstep. zsh. zstep. try th_if_lit.
    zstep. rewrite (t_sx32_small (num + 1)) by lia.
    do 13 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (JOIN mm ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [junk' DJ] end.
    apply evt_done; do 6 eexists; split; [cbv delta [mkR]; reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [assumption|]; split; [assumption|]. split; [assumption| exact DJ].
  - zstep. th_if_lit.
    zstep. if_cases K7; zify_cond K7.
    { exfalso. rewrite ?SGS in K7 by lia. apply andb_false_iff in K7. destruct K7 as [K7|K7]; apply Z.ltb_ge in K7; clear - K7 NUM NA NAL; lia. }
    zstep. zstep. zstep. zstep. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep. zsh. zstep. try th_if_lit.
    zstep. th_fix_lit_store.
    zstep. zsh. zstep. try th_if_lit.
    zstep. rewrite (t_sx32_small (num + 1)) by lia.
    do 13 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (JOIN mm ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [junk' DJ] end.
    apply evt_done; do 6 eexists; split; [cbv delta [mkR]; reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [assumption|]; split; [assumption|]. split; [assumption| exact DJ].
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
  intros until copyt. intros AHI AAL ALO HC ACC D0 DR UT SHC ST LO0 LO HTOP MI.
  unfold e_sk_reserve, sk_cells, g_shadow_memory_dynamic_address, SHB, SITE_skr_realloc, SK_FILE, e_CRYPTO_realloc_array in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 11 zstep.
  do 3 zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small 4) by lia.
  (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit.
  zstep.
  zstep. zstep. th_if_lit.
  do 4 zstep. zstep. th_if_lit. zstep.
  zstep. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; exact (D0 K5)|].
  do 4 zstep. zstep. th_if_lit. zstep. rewrite (t_sx32_small 4) by lia.
  zstep. th_if_lit.
  zstep. th_if_lit.
  (* [comment removed for export] *)
  do 9 zstep. zstep. th_if_lit.
  do 6 zstep. zstep. th_if_lit.
  do 5 zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; assumption.
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
  intros until s7v. intros AHI AAL ALO HC ACC QR UT SHC FR ST LO0 LO HTOP MI. unfold sk_cells, g_shadow_memory_dynamic_address, SHB, SITE_skr_realloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(A + 8, A + 16); (A + 20, A + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-80) EU1.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zstep. zsh. zstep. th_if_lit.
  zstep.
  zstep. zsh. zstep. th_if_lit.
  zstep. th_fix_lit_store.
  zstep. do 9 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; assumption.
Qed.
