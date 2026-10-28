(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_getrn Fz_I1_split Fz_I1_expand Fz_env Fz_M_malloc Fz_M_realloc Fz_M_realloc_array Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_lh_insert : Z := 0x2003c8.
Definition LHI_EXPAND : Z := 0x2004cc.      (* [comment removed for export] *)

Lemma m_divu : forall a b : word, bv_unsigned b <> 0 -> mul_div Instr.M_DIVU a b = Z_to_bv 64 (bv_unsigned a / bv_unsigned b).
Proof.
  intros a b Hb. unfold mul_div. destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|_]; [contradiction|].
  apply bv_eq. rewrite bv_divu_unsigned, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ a) as RA. pose proof (bv_unsigned_in_range _ b) as RB.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Definition lhi_frame (jl : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 88 jl; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition lhi_w0_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (lh data B nn na p pmax items : Z) (x40 x48 pad : word) : machine_state -> Prop :=
  fun ms => exists (jl : list byte) (m' : mem),
    ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 0x7fff8000))
                 (Z_to_bv 64 512) (Z_to_bv 64 (items * 256 / nn)) (Z_to_bv 64 nn) a3 a4 a5 a6 a7
                 (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh + 96))
                 (Z_to_bv 64 ((lh + 88) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 0x7fff8000) s10 s11 t3 t4 t5 t6)
            F (if 512 <=? items * 256 / nn then Z_to_bv 64 LHI_EXPAND else Z_to_bv 64 LHI_SPLIT_EXIT) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 192, bv_unsigned sp); (lh + 96, lh + 100)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -192) (lhi_frame jl ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    /\ rw_cells asegs m' lh (lhs_cells B nn na p pmax items x40 x48 (Z_to_bv 64 0) pad)
    /\ stk asegs m' lo (bv_unsigned sp + -192).

Lemma lhi_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh data B nn na p pmax items : Z) (x40 x48 err pad : word),
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 data ->
  rw_cells asegs m lh (lhs_cells B nn na p pmax items x40 x48 err pad) -> 0 < nn < 2^31 -> 0 <= items < 2^40 ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> 0x10007fff8000 <= lh -> lh + 104 <= lo ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (lhi_w0_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m lh data B nn na p pmax items x40 x48 pad)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_lh_insert) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros -> -> SC NN IT ACL ALL HIL LLO UT SHC ST LO0 LO HTOP MI.
  unfold lhs_cells in SC. unfold g_shadow_memory_dynamic_address, SHB in SHC. unfold e_lh_insert.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp); (lh + 96, lh + 100)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 192%nat [88; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 15 zstep.
  do 9 zstep. zstep. th_if_lit.
  zstep. th_fix_lit_store.
  do 4 zstep. zstep. th_if_lit.
  do 4 zstep. zstep. th_if_lit. do 6 zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  rewrite (zx32_small nn) by lia. rewrite m_divu by (rewrite unsigned_lit by lia; lia). rewrite (unsigned_lit nn) by lia.
  rewrite (Z.shiftl_mul_pow2 items 8) by lia. change (2 ^ 8) with 256. rewrite (unsigned_lit (items * 256)) by lia.
  zstep.
  assert (QB : 0 <= items * 256 / nn < 2^48) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; [lia| nia]]).
  replace (negb (bv_ltu (Z_to_bv 64 (items * 256 / nn)) (Z_to_bv 64 512))) with (512 <=? items * 256 / nn)
    by (unfold bv_ltu; rewrite !unsigned_lit by lia; destruct (Z.ltb_spec (items * 256 / nn) 512); destruct (Z.leb_spec 512 (items * 256 / nn)); cbn; lia).
  apply evt_done. unfold lhi_w0_post, lhi_frame, lhs_cells, LHI_EXPAND, LHI_SPLIT_EXIT. do 2 eexists.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition lhi_locals (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; CB 8 j10].

(* [comment removed for export] *)
Definition lhi_w1_post (ra sp gp tp t0 t1 t2 a1 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (lh data nn na p pmax : Z) (j0 j1 j2 j3 j4 j5 : list byte) (hs : word) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 0x7fff8000))
                 (Z_to_bv 64 (lh + 64)) a1 (Z_to_bv 64 0) (Z_to_bv 64 (p + 1)) (Z_to_bv 64 (lh + 60)) (Z_to_bv 64 ((lh + 60) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 (lh ≫ 3)) a7
                 (Z_to_bv 64 pmax) (Z_to_bv 64 ((lh + 64) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh + 96))
                 (Z_to_bv 64 ((lh + 68) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 (lh + 68)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 na) (Z_to_bv 64 p) t3 t4 t5 t6)
            F (if p + 1 <? pmax then Z_to_bv 64 LHI_SPLIT_PRE else Z_to_bv 64 0x200530) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 192, bv_unsigned sp - 104)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -192) ([CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5] ++ lhi_spill lh data ++ [C8 hs])
    /\ stk asegs m' lo (bv_unsigned sp + -192).

Lemma lhi_w1 : forall (ra sp gp tp t0 t1 t2 s10 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh data B nn na p pmax items : Z) (x40 x48 err pad : word) (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 : list byte) (hs : word),
  rw_cells asegs m lh (lhs_cells B nn na p pmax items x40 x48 err pad) -> 0 < na < 2^31 -> 0 <= p < 2^31 - 1 -> 0 < pmax < 2^31 ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> 0x10007fff8000 <= lh -> lh + 104 <= lo ->
  rw_cells asegs m (bv_unsigned sp + -192) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; C8 hs] ->
  stk asegs m lo (bv_unsigned sp + -192) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (lhi_w1_post ra sp gp tp t0 t1 t2 a1 a7 t3 t4 t5 t6 F fc lo m lh data nn na p pmax j0 j1 j2 j3 j4 j5 hs)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 0x7fff8000))
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh + 96))
               (Z_to_bv 64 ((lh + 88) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 0x7fff8000) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LHI_EXPAND) fc None m (seg_rom asegs)).
Proof.
  intros until hs. intros SC NA PP PM ACL ALL HIL LLO FRL ST LO0 LO HTOP MI.
  unfold lhs_cells in SC. unfold LHI_EXPAND.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp - 104)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) 0 EU0. rewrite Z.add_0_r in EU0. cl_eu (bv_unsigned sp) (-192) EU1.
  (* [comment removed for export] *)
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  do 5 zstep. zstep. th_if_lit.
  do 6 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small pmax) by lia. zstep. zstep. zstep.
  rewrite !(zx32_small p) by lia. rewrite !(zx32_small na) by lia. rewrite (unsigned_lit p) by lia.
  assert (SWR : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z).
  { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z. rewrite Z.mod_small by lia. lia. }
  rewrite !SWR by lia. replace (bv_ltu (Z_to_bv 64 (p + 1)) (Z_to_bv 64 pmax)) with (p + 1 <? pmax) by (unfold bv_ltu; rewrite !unsigned_lit by lia; reflexivity).
  change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). apply evt_done. unfold lhi_w1_post, lhi_spill, LHI_SPLIT_PRE. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [cbn [app]; exact FRL| assumption].
Qed.

Definition SITE_lhi_realloc : Z := 0x200578.   (* [comment removed for export] *)
Definition LHI_FILE : Z := 0x4a700.            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lhi_w1b_post (sp gp tp t0 t1 t2 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (lh data B na p pmax : Z) (hs : word) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_lhi_realloc) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 0x7fff8000))
                 (Z_to_bv 64 B) (Z_to_bv 64 (2 * na)) (Z_to_bv 64 8) (Z_to_bv 64 LHI_FILE) (Z_to_bv 64 253) (Z_to_bv 64 ((lh + 60) ≫ 3 + 2147450880)) (Z_to_bv 64 (lh ≫ 3)) a7
                 (Z_to_bv 64 pmax) (Z_to_bv 64 ((lh + 64) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh ≫ 3 + 0x7fff8000))
                 (Z_to_bv 64 ((lh + 68) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 (lh + 68)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 na) (Z_to_bv 64 p) t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_realloc_array) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 192, bv_unsigned sp - 104)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -192)
         ([C8 (Z_to_bv 64 (2 * na)); C8 (Z_to_bv 64 (lh ≫ 3)); C8 (Z_to_bv 64 ((lh + 60) ≫ 3 + 2147450880)); C8 (Z_to_bv 64 (lh + 60)); C8 (Z_to_bv 64 (lh + 64)); C8 (Z_to_bv 64 (lh + 96))]
          ++ lhi_spill lh data ++ [C8 hs])
    /\ stk asegs m' lo (bv_unsigned sp + -192).

Lemma lhi_w1b : forall (sp gp tp t0 t1 t2 ra a1 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh data B nn na p pmax items : Z) (x40 x48 err pad : word) (j0 j1 j2 j3 j4 j5 : list byte) (hs : word),
  rw_cells asegs m lh (lhs_cells B nn na p pmax items x40 x48 err pad) -> 0 < na < 2^31 -> 0 <= p < 2^31 - 1 -> 0 < pmax < 2^31 -> 0 < B < 2^64 ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> 0x10007fff8000 <= lh -> lh + 104 <= lo ->
  rw_cells asegs m (bv_unsigned sp + -192) ([CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5] ++ lhi_spill lh data ++ [C8 hs]) ->
  stk asegs m lo (bv_unsigned sp + -192) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (lhi_w1b_post sp gp tp t0 t1 t2 a7 t3 t4 t5 t6 F fc lo m lh data B na p pmax hs)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 0x7fff8000))
               (Z_to_bv 64 (lh + 64)) a1 (Z_to_bv 64 0) (Z_to_bv 64 (p + 1)) (Z_to_bv 64 (lh + 60)) (Z_to_bv 64 ((lh + 60) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 (lh ≫ 3)) a7
               (Z_to_bv 64 pmax) (Z_to_bv 64 ((lh + 64) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh + 96))
               (Z_to_bv 64 ((lh + 68) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 (lh + 68)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 na) (Z_to_bv 64 p) t3 t4 t5 t6)
          F (Z_to_bv 64 0x200530) fc None m (seg_rom asegs)).
Proof.
  intros until hs. intros SC NA PP PM BB ACL ALL HIL LLO FRL ST LO0 LO HTOP MI.
  unfold lhs_cells in SC. unfold lhi_spill in FRL. cbn [app] in FRL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp - 104)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) 0 EU0. rewrite Z.add_0_r in EU0. cl_eu (bv_unsigned sp) (-192) EU1.
  do 5 zstep.
  zstep. zstep. zstep. th_if_lit.
  zstep. zstep. rewrite (Z.shiftl_mul_pow2 na 1) by lia. change (2 ^ 1) with 2. replace (na * 2) with (2 * na) by lia.
  zstep. zstep. zstep.
  change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. rewrite (Z.mod_small (2 * na)) by lia. do 4 zstep. zstep.
  apply evt_done. unfold lhi_w1b_post, lhi_spill, SITE_lhi_realloc, LHI_FILE, e_CRYPTO_realloc_array. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [cbn [app]; exact FRL| assumption].
Qed.
Definition SITE_lhi_memset : Z := 0x200594.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lhi_w2_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lh q nn na p pmax items : Z) (x40 x48 pad : word) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_lhi_memset) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 0x7fff8000))
                 (Z_to_bv 64 (q + 8 * na)) (Z_to_bv 64 0) (Z_to_bv 64 (8 * na)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 pmax) (Z_to_bv 64 ((lh + 64) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh ≫ 3 + 0x7fff8000))
                 (Z_to_bv 64 ((lh + 68) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 (lh + 68)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 na) (Z_to_bv 64 p) t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memset) fc None m' (seg_rom asegs)
    /\ munch [(lh, lh + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' lh (lhs_cells q nn na p pmax items x40 x48 (Z_to_bv 64 0) pad).

Lemma lhi_w2 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh q B nn na p pmax items : Z) (x40 x48 pad : word),
  rw_cells asegs m lh (lhs_cells B nn na p pmax items x40 x48 (Z_to_bv 64 0) pad) -> 0 < na < 2^31 -> 0 < q -> q + 16 * na <= 2^47 ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> 0x10007fff8000 <= lh -> lh + 104 <= lo ->
  rw_cells asegs m (bv_unsigned sp + -152) [C8 (Z_to_bv 64 (lh + 96))] ->           (* [comment removed for export] *)
  stk asegs m lo (bv_unsigned sp + -192) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (lhi_w2_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m lh q nn na p pmax items x40 x48 pad)
      (MS (mkR (Z_to_bv 64 SITE_lhi_realloc) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 0x7fff8000))
               (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 pmax) (Z_to_bv 64 ((lh + 64) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh ≫ 3 + 0x7fff8000))
               (Z_to_bv 64 ((lh + 68) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 (lh + 68)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 na) (Z_to_bv 64 p) t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_lhi_realloc) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros SC NA Q0 QT ACL ALL HIL LLO FR152 ST LO0 LO HTOP MI.
  unfold lhs_cells in SC. unfold SITE_lhi_realloc.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(lh, lh + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  cl_eu (bv_unsigned sp) 0 EU0. rewrite Z.add_0_r in EU0.
  zstep. zstep. th_if_lit.
  zstep. zstep. rewrite (Z.shiftl_mul_pow2 na 3) by lia. change (2 ^ 3) with 8. replace (na * 8) with (8 * na) by lia.
  zstep. zstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
  apply evt_done. unfold lhi_w2_post, lhs_cells, SITE_lhi_memset, e_asan_memset. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.
(* [comment removed for export] *)
Definition lhi_w3_post (sp gp tp t0 t1 t2 a5 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lh q nn na p pmax items : Z) (x40 x48 pad : word) : machine_state -> Prop :=
  fun ms => exists (a2' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_lhi_memset) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 0x7fff8000))
                 (Z_to_bv 64 (lh + 64)) (Z_to_bv 64 (2 * na)) a2' (Z_to_bv 64 0) (Z_to_bv 64 (lh + 60)) a5 (Z_to_bv 64 (lh ≫ 3)) a7
                 (Z_to_bv 64 pmax) (Z_to_bv 64 ((lh + 64) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh + 96))
                 (Z_to_bv 64 ((lh + 68) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 (lh + 68)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 na) (Z_to_bv 64 p) t3 t4 t5 t6)
            F (Z_to_bv 64 LHI_SPLIT_PRE) fc None m' (seg_rom asegs)
    /\ munch [(lh + 60, lh + 64); (lh + 68, lh + 72)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' lh (lhs_cells q nn (2 * na) p na items x40 x48 (Z_to_bv 64 0) pad).

Lemma lhi_w3 : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh data q nn na p pmax items : Z) (x40 x48 pad hs : word),
  rw_cells asegs m lh (lhs_cells q nn na p pmax items x40 x48 (Z_to_bv 64 0) pad) -> 0 < na < 2^30 ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> 0x10007fff8000 <= lh -> lh + 104 <= lo ->
  rw_cells asegs m (bv_unsigned sp + -192)
    ([C8 (Z_to_bv 64 (2 * na)); C8 (Z_to_bv 64 (lh ≫ 3)); C8 (Z_to_bv 64 ((lh + 60) ≫ 3 + 2147450880)); C8 (Z_to_bv 64 (lh + 60)); C8 (Z_to_bv 64 (lh + 64)); C8 (Z_to_bv 64 (lh + 96))]
     ++ lhi_spill lh data ++ [C8 hs]) ->
  stk asegs m lo (bv_unsigned sp + -192) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (lhi_w3_post sp gp tp t0 t1 t2 a5 a7 t3 t4 t5 t6 F fc m lh q nn na p pmax items x40 x48 pad)
      (MS (mkR (Z_to_bv 64 SITE_lhi_memset) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 0x7fff8000))
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 pmax) (Z_to_bv 64 ((lh + 64) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh ≫ 3 + 0x7fff8000))
               (Z_to_bv 64 ((lh + 68) ≫ 3 + 0x7fff8000)) (Z_to_bv 64 (lh + 68)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 na) (Z_to_bv 64 p) t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_lhi_memset) fc None m (seg_rom asegs)).
Proof.
  intros until hs. intros SC NA ACL ALL HIL LLO FRL ST LO0 LO HTOP MI.
  unfold lhs_cells in SC. unfold lhi_spill in FRL. cbn [app] in FRL. unfold SITE_lhi_memset.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(lh + 60, lh + 64); (lh + 68, lh + 72)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) 0 EU0. rewrite Z.add_0_r in EU0.
  zstep. zstep. th_if_lit. zstep.
  do 6 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word).
  apply evt_done. unfold lhi_w3_post, lhs_cells, LHI_SPLIT_PRE, SITE_lhi_memset. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.
