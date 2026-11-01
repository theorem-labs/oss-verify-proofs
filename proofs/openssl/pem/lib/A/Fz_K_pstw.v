(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Th_mutex Fz_T_lock Fz_env Fz_M_malloc Fz_T_sk Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_skw Fz_K_sk Fz_I2_ppis Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Definition e_property_string : Z := 0x20c090.
Definition e_property_name : Z := 0x20c068.
Definition e_property_value : Z := 0x20c6fc.
Definition e_get_data : Z := 0x1f77d0.
Definition e_lh_error : Z := 0x201498.
Definition SITE_ps_smalloc : Z := 0x20c10c.
Definition SITE_ps_getdata : Z := 0x20c1a0.
Definition SITE_ps_rlock : Z := 0x20c1f4.
Definition SITE_ps_retr1 : Z := 0x20c208.
Definition SITE_ps_unlock1 : Z := 0x20c284.
Definition SITE_ps_wlock : Z := 0x20c29c.
Definition SITE_ps_retr2 : Z := 0x20c2e8.
Definition SITE_ps_strlen : Z := 0x20c2f4.
Definition SITE_ps_malloc : Z := 0x20c30c.
Definition SITE_ps_memcpy : Z := 0x20c328.
Definition SITE_ps_push : Z := 0x20c490.
Definition SITE_ps_insert : Z := 0x20c4a8.
Definition SITE_ps_lherr : Z := 0x20c4b0.
Definition SITE_ps_unlock2 : Z := 0x20c220.
Definition PS_FILE : Z := 0x4b980.
Definition PS_MAGIC : Z := 0x41b58ab3.
Definition PS_DESCR : Z := 0x2ba37.
Definition PS_RETIRED : Z := 0x45e0360e.
Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).

(* [comment removed for export] *)
Lemma gd3_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo ps : Z),
  a0 = Z_to_bv 64 PPI_CTX -> a1 = Z_to_bv 64 3 ->
  rw_cells asegs m CTX_PSD [C8 (Z_to_bv 64 ps)] -> ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ps) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_get_data) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ps
    CTXARG IDXARG SLOT SLOTSH UNT SHDYN STK LOBIG LOSP SPTOP MINV.
  subst a0 a1.
  unfold e_get_data, PPI_CTX. unfold CTX_PSD in SLOT. unfold g_shadow_memory_dynamic_address, SHB in SHDYN.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (UTF : ut_fp [(bv_unsigned sp - 32, bv_unsigned sp)]) by ut_fp_lia.
  carve_frame 32%nat STK.
  (* the context is not NULL, then the index 3 is in the jump table range *)
  repeat zstep. if_true.
  repeat zstep. if_false.
  (* case 3 of the table: the shadow byte of the field is zero *)
  repeat zstep. if_true.
  repeat zstep.
  release_frame FR STK (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Lemma lherr_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh B items : Z),
  a0 = Z_to_bv 64 lh -> rw_cells asegs m lh (plh_cells B items) -> acc asegs m lh 104 -> 0 < lh -> lh mod 8 = 0 -> lh + 104 <= lo ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a1' a2' : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_lh_error) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lh B items
    TABLEARG TABLE TABLEACC TABLEPOS TABLEAL TABLELO UNT SHDYN STK LOBIG LOSP SPTOP MINV.
  subst a0. unfold e_lh_error, plh_cells in *.
  unfold g_shadow_memory_dynamic_address, SHB in SHDYN.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (UTF : ut_fp [(bv_unsigned sp - 16, bv_unsigned sp)]) by ut_fp_lia.
  assert (SHF : sh_fp [(bv_unsigned sp - 16, bv_unsigned sp)]) by sh_fp_lia.
  carve_frame 16%nat STK.
  (* the shadow byte of the error field is zero, so the check passes *)
  repeat zstep. zsh. if_false.
  repeat zstep.
  release_frame FR STK (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition ps_ftail (s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

(* [comment removed for export] *)
Definition ps_w0_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (C NM CR S : Z) (F : bvmap 5 word) (fc : bv 32) (lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ps_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
               (Z_to_bv 64 64) a1' a2' (Z_to_bv 64 S) a4 a5 a6 a7 s2 (Z_to_bv 64 C) s4 (Z_to_bv 64 S) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 NM) (Z_to_bv 64 CR)
               s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m'
    /\ wmono asegs m m'
    /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (C8 (Z_to_bv 64 0) :: CB 48 j :: ps_ftail s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160)
    /\ stk asegs m' lo (bv_unsigned sp + -160 - pd).

Lemma ps_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd C NM CR S : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd -> 0 <= C < 2^64 -> 0 <= NM < 2^64 -> 0 <= CR < 2^64 -> 0 <= S < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (ps_w0_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 C NM CR S F fc lo pd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 NM) (Z_to_bv 64 CR) (Z_to_bv 64 S) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_property_string) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd C NM CR S
    PADCASE PADMOD CRANGE NMRANGE CRRANGE SRANGE STK LOSP LOBIG SPTOP UNT SHDYN UAR MINV.
  unfold e_property_string, ps_w0_post.
  unfold g_shadow_memory_dynamic_address in SHDYN. unfold g_detect_stack_use_after_return in UAR.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (UTF : ut_fp [(bv_unsigned sp - 160, bv_unsigned sp)]) by ut_fp_lia.
  carve_frame 160%nat STK.
  (* andi sp, sp, -32 drops the frame base by the padding pd *)
  assert (REALIGN : Z.land (bv_unsigned sp + -160) 18446744073709551584 = bv_unsigned sp + -160 - pd).
  { change 18446744073709551584 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 5))).
    rewrite Z.land_assoc, Z.land_ones by lia. rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    rewrite Z.mod_small by lia. change (2 ^ 5) with 32. Z.div_mod_to_equations. lia. }
  (* the first store writes the zero register *)
  zstep. zstep. fix_lit_store.
  repeat zstep. rewrite REALIGN.
  (* detect_stack_use_after_return is 1: take the fake-stack call *)
  if_false. do 2 zstep.
  pose proof (stk_split asegs _ lo (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) STK ltac:(lia)) as [BELOW PAD].
  finish.
  exact FR.
Qed.

(* [comment removed for export] *)
Definition psd_cells (pk pl1 pl2 ni vi pq1 pq2 : Z) : list cell :=
  [C8 (Z_to_bv 64 pk); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); C4 (Z_to_bv 64 ni); C4 (Z_to_bv 64 vi); C8 (Z_to_bv 64 pq1); C8 (Z_to_bv 64 pq2)].
(* [comment removed for export] *)
Definition ps_fcells (hj : list byte) (sv : word) (pj tj : list byte) : list cell :=
  [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj; C8 sv; CB 8 pj; CB 8 tj].
Definition ps_shadow : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
Definition nmz (nm : bool) : Z := if nm then 1 else 0.
Definition t_of (nm : bool) (pl1 pl2 : Z) : Z := if nm then pl1 else pl2.
Definition q_of (nm : bool) (pq1 pq2 : Z) : Z := if nm then pq1 else pq2.
Definition off_idx (nm : bool) : Z := if nm then 24 else 28.

Lemma ps_acc16 : forall (m : mem) f, f mod 64 = 0 -> 0 < f -> rw_cells asegs m (shad f) ps_shadow -> acc asegs m (f + 32) 16.
Proof.
  intros m f ALIGNED POSITIVE POISON k KRANGE.
  destruct POISON as ((_ & SHLO & SHHI & SHBYTES) & _).
  unfold ps_shadow in SHHI, SHBYTES. cbn [cells_bytes cbytes app length] in SHHI, SHBYTES.
  assert (GRANULE : shad (f + 32 + k) = shad f + Z.of_nat (4 + Z.to_nat (k / 8))).
  { unfold shad. assert (0 <= k / 8 <= 1) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
  exists (Z_to_bv 8 0). split; [| left; reflexivity].
  assert (KDIV : k / 8 = 0 \/ k / 8 = 1) by (Z.div_mod_to_equations; lia).
  split; [rewrite GRANULE; lia|]. split; [cbn [length]; rewrite GRANULE; destruct KDIV as [E|E]; rewrite E; cbn; lia|].
  intros n NLT. cbn [length] in NLT. replace n with 0%nat by lia. rewrite Z.add_0_r, GRANULE.
  rewrite SHBYTES by (destruct KDIV as [E|E]; rewrite E; cbn; lia).
  destruct KDIV as [E|E]; rewrite E; reflexivity.
Qed.

(* [comment removed for export] *)
Definition ps_w1a_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (f lo pd : Z) (fj : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j hj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ps_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
               (Z_to_bv 64 (-15)) (Z_to_bv 64 PS_DESCR) (Z_to_bv 64 e_property_string) a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9
               (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6) F (Z_to_bv 64 0x20c194) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (bv_unsigned sp - 128, bv_unsigned sp - 104)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (CB 56 j :: ps_ftail s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160)
    /\ stk asegs m' lo (bv_unsigned sp + -160 - pd)
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 32 hj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) ps_shadow.

Lemma ps_w1a : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (f lo pd : Z) (j fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 56 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -160) (C8 (Z_to_bv 64 0) :: CB 48 j :: ps_ftail s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) -> stk asegs m lo (bv_unsigned sp + -160 - pd) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (shad f) [CB 8 sj] -> mem_inv asegs m ->
  evt asegs (ps_w1a_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 t3 t4 t5 t6 F fc rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v f lo pd fj m)
    (MS (mkR (Z_to_bv 64 SITE_ps_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ps_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v f lo pd j fj sj
    PADCASE FPOS FALIGN FIMG FLO FSHAD LOSP LOBIG SPTOP SAVED PAD BELOW FAKE FAKESH MINV.
  unfold ps_w1a_post, SITE_ps_smalloc. unfold ps_ftail in SAVED. unfold shad, SHB in FAKESH.
  pose proof (munch_refl [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (bv_unsigned sp - 128, bv_unsigned sp - 104)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* the store to 48(s1) needs a chunk based at the realigned stack pointer *)
  destruct PADCASE as [PD | PD].
  - assert (LOCAL : rw_cells asegs m (bv_unsigned sp + -160 - pd)
      [C8 (Z_to_bv 64 0); CB 48 j; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      by (rewrite PD, Z.sub_0_r; exact SAVED).
    clear SAVED.
    repeat zstep.
    rewrite (ubs_eqb0_false_lit f) by lia. cbn [negb].
    zstep. do 12 (zstep; fix_lit_store).
    rewrite (shadow_spell1 f) by lia.
    do 9 (zstep; fix_lit_store;
          try (match goal with |- context [le1 (Z_to_bv 64 ?z)] =>
                 replace (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]
                   by (unfold le1; rewrite unsigned_lit_wrap; cbn -[Z_to_bv]; f_equal; apply Z_to_bv8_mod; reflexivity);
                 mem_after_store end)).
    apply evt_done.
    match type of LOCAL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?rest) =>
      pose proof (rw_cells_merge asegs _ _ [] [c1; c2; c3] rest LOCAL) as MERGED end.
    cbn [app cells_size csize Nat.add] in MERGED.
    replace (bv_unsigned sp + -160 - pd) with (bv_unsigned sp + -160) in MERGED by lia.
    replace (f / 8 + 2147450888) with (f / 8 + 2147450880 + 8) by lia.
    do 3 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption.
  - destruct (stk_carve asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) 16 PAD ltac:(lia)) as [_ (pad & PADC)].
    replace (bv_unsigned sp + -160 - Z.of_nat 16) with (bv_unsigned sp + -160 - pd) in PADC by lia.
    assert (LOCAL : rw_cells asegs m (bv_unsigned sp + -160 - pd)
      [CB 16 pad; C8 (Z_to_bv 64 0); CB 48 j; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]).
    { apply (proj2 (rw_cells_app m _ [CB 16 pad] _)). split; [exact PADC|]. cbn [cells_size csize Nat.add].
      replace (bv_unsigned sp + -160 - pd + Z.of_nat 16) with (bv_unsigned sp + -160) by lia. exact SAVED. }
    clear SAVED PADC.
    repeat zstep.
    rewrite (ubs_eqb0_false_lit f) by lia. cbn [negb].
    zstep. do 12 (zstep; fix_lit_store).
    rewrite (shadow_spell1 f) by lia.
    do 9 (zstep; fix_lit_store;
          try (match goal with |- context [le1 (Z_to_bv 64 ?z)] =>
                 replace (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]
                   by (unfold le1; rewrite unsigned_lit_wrap; cbn -[Z_to_bv]; f_equal; apply Z_to_bv8_mod; reflexivity);
                 mem_after_store end)).
    apply evt_done.
    apply rw_cells_tail in LOCAL. cbn [csize] in LOCAL.
    match type of LOCAL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
      pose proof (rw_cells_merge asegs _ _ [] [c1; c2; c3; c4] rest LOCAL) as MERGED end.
    cbn [app cells_size csize Nat.add] in MERGED.
    replace (bv_unsigned sp + -160 - pd + Z.of_nat 16) with (bv_unsigned sp + -160) in MERGED by lia.
    replace (f / 8 + 2147450888) with (f / 8 + 2147450880 + 8) by lia.
    do 3 eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption.
Qed.

(* [comment removed for export] *)
Lemma ps_fsplit : forall (m : mem) f hj,
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 32 hj] ->
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 (firstn 8 hj)]
  /\ rw_cells asegs m (f + 32) [CB 8 (firstn 8 (skipn 8 hj))] /\ rw_cells asegs m (f + 40) [CB 16 (firstn 16 (skipn 8 (skipn 8 hj)))].
Proof.
  intros m f hj WHOLE.
  pose proof (rw_cells_split_CB asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string)] 32 hj []
                [8; 8; 16]%nat WHOLE eq_refl) as PIECES.
  cbn [mk_CB_cells app] in PIECES.
  apply (proj1 (rw_cells_app m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 (firstn 8 hj)] _)) in PIECES.
  destruct PIECES as [HEAD REST]. cbn [cells_size csize Nat.add] in REST.
  apply (proj1 (rw_cells_app m _ [CB 8 (firstn 8 (skipn 8 hj))] _)) in REST.
  destruct REST as [MIDDLE LAST]. cbn [cells_size csize Nat.add] in LAST.
  split; [exact HEAD|]. split.
  - replace (f + 32) with (f + Z.of_nat 32) by reflexivity. exact MIDDLE.
  - replace (f + 40) with (f + Z.of_nat 32 + Z.of_nat 8) by (cbn; lia). exact LAST.
Qed.

Lemma ps_fjoin : forall (m : mem) f hj1 (sv : word) hj2,
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1] ->
  rw_cells asegs m (f + 32) [C8 sv] -> rw_cells asegs m (f + 40) [CB 16 hj2] ->
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 sv; CB 16 hj2].
Proof.
  intros m f hj1 sv hj2 HEADER SLOT TAIL.
  assert (UPPER : rw_cells asegs m (f + 32) [C8 sv; CB 16 hj2]).
  { apply rw_cells_join2; [exact SLOT|]. cbn [csize]. replace (f + 32 + Z.of_nat 8) with (f + 40) by (cbn; lia). exact TAIL. }
  apply (proj2 (rw_cells_app m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1] [C8 sv; CB 16 hj2])).
  split; [exact HEADER|]. cbn [cells_size csize Nat.add]. exact UPPER.
Qed.

(* [comment removed for export] *)
Definition ps_w1b_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (nm : bool)
    (f lo pd S ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j hj1 hj2 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ps_strlen) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
               (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 S)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 (t_of nm pl1 pl2)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880))
               (Z_to_bv 64 f) t3 t4 t5 t6)
            F (Z_to_bv 64 e_strlen) fc None m' (seg_rom asegs)
    /\ munch [(f + 32, f + 40); (bv_unsigned sp + -160 - pd - 144, bv_unsigned sp + -160 - pd + 32); (pk + 4, pk + 8)] m m'
    /\ wmono asegs m m'
    /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (CB 56 j :: ps_ftail s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160)
    /\ stk asegs m' lo (bv_unsigned sp + -160 - pd)
    /\ rw_cells asegs m' (bv_unsigned sp + -160 - pd + 8) [C8 (Z_to_bv 64 (off_idx nm))]
    /\ rw_cells asegs m' (bv_unsigned sp + -160 - pd + 16) [C8 (Z_to_bv 64 (nmz nm))]
    /\ rw_cells asegs m' (bv_unsigned sp + -160 - pd + 24) [C8 (Z_to_bv 64 (t_of nm pl1 pl2))]
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 (Z_to_bv 64 S); CB 16 hj2]
    /\ rw_cells asegs m' (f / 8 + 2147450880) ps_shadow
    /\ rw_cells asegs m' CTX_PSD [C8 (Z_to_bv 64 ps)]
    /\ rw_cells asegs m' ps (psd_cells pk pl1 pl2 ni vi pq1 pq2)
    /\ rw_cells asegs m' pk (mutex_cells z64 (Z_to_bv 64 16))
    /\ plh_rep m' (t_of nm pl1 pl2) B items bks.

Lemma ps_w1b : forall (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (nm : bool) (lo pd f S ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (str : list byte) (j hj : list byte)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  (pd = 0 \/ pd = 16) -> (bv_unsigned sp + -160 - pd) mod 32 = 0 ->
  0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 56 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 320 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -160) (CB 56 j :: ps_ftail s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) -> stk asegs m lo (bv_unsigned sp + -160 - pd) ->
  acc asegs m (bv_unsigned sp + -160 - pd - 144) 144 ->
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 32 hj] ->
  rw_cells asegs m (f / 8 + 2147450880) ps_shadow ->
  rw_cells asegs m CTX_PSD [C8 (Z_to_bv 64 ps)] -> ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m ps (psd_cells pk pl1 pl2 ni vi pq1 pq2) -> acc asegs m ps 48 -> 0 < ps -> ps mod 16 = 0 -> ps + 48 <= lo -> 0x10007fff8000 <= ps -> (ps + 48 <= f \/ f + 64 <= ps) ->
  rw_cells asegs m pk (mutex_cells z64 z64) -> 0 < pk -> pk mod 16 = 0 -> pk + 40 <= lo -> 0x10007fff8000 <= pk -> (pk + 40 <= f \/ f + 64 <= pk) ->
  plh_rep m (t_of nm pl1 pl2) B items bks ->
  acc asegs m (t_of nm pl1 pl2) 104 -> 0 < t_of nm pl1 pl2 -> t_of nm pl1 pl2 + 104 <= lo -> (t_of nm pl1 pl2 + 104 <= f \/ f + 64 <= t_of nm pl1 pl2) ->
  acc asegs m B 128 -> 0 < B -> B + 128 <= lo -> (B + 128 <= f \/ f + 64 <= B) ->
  (forall n, In n (concat bks) -> acc asegs m (fst n) 24 /\ 0 < fst n /\ fst n + 24 <= lo /\ (fst n + 24 <= f \/ f + 64 <= fst n) /\ (fst n + 24 <= pk \/ pk + 40 <= fst n)) ->
  0 < S -> bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 20 ->
  acc asegs m S (Z.of_nat (length str) + 1) -> S + Z.of_nat (length str) + 1 <= 0xbc6000 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  (ps + 48 <= t_of nm pl1 pl2 \/ t_of nm pl1 pl2 + 104 <= ps) -> (pk + 40 <= t_of nm pl1 pl2 \/ t_of nm pl1 pl2 + 104 <= pk) ->
  (ps + 48 <= pk \/ pk + 40 <= ps) -> (pk + 40 <= B \/ B + 128 <= pk) ->
  mem_inv asegs m ->
  evt asegs (ps_w1b_post sp gp tp F fc rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v nm f lo pd S ps pk pl1 pl2 ni vi pq1 pq2 B items bks m)
    (MS (mkR (Z_to_bv 64 SITE_ps_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
             (Z_to_bv 64 (-15)) (Z_to_bv 64 PS_DESCR) (Z_to_bv 64 e_property_string) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 PPI_CTX) s4 (Z_to_bv 64 S) (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 1) s9 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
        F (Z_to_bv 64 0x20c194) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s9 t3 t4 t5 t6 F fc m nm lo pd f S ps pk pl1 pl2 ni vi pq1 pq2 B items bks str j hj
    rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
    PADCASE RALIGN FPOS FALIGN FIMG FLO FSHAD LOSP LOBIG SPTOP UNT SHDYN SAVED PAD BELOW CALLEEACC
    FAKE FAKESH CTXSLOT CTXSH PSD PSACC PSPOS PSAL PSLO PSHI PSFAKE
    LOCK PKPOS PKAL PKLO PKHI PKFAKE TABLE TABLEACC TABLEPOS TABLELO TABLEFAKE BUCKETACC BPOS BLO BFAKE NODES
    SPOS SBYTES SNONUL SNE SLEN SACC SLOW MISS PSTABLE PKTABLE PSPK PKB MINV.
  unfold ps_w1b_post. unfold ps_ftail in SAVED.
  unfold g_shadow_memory_dynamic_address, SHB in SHDYN.
  unfold psd_cells in PSD. unfold mutex_cells in LOCK. unfold ps_shadow in FAKESH. unfold CTX_PSD in CTXSLOT.
  pose proof (munch_refl [(f + 32, f + 40); (bv_unsigned sp + -160 - pd - 144, bv_unsigned sp + -160 - pd + 32); (pk + 4, pk + 8)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (UTF : ut_fp [(f + 32, f + 40); (bv_unsigned sp + -160 - pd - 144, bv_unsigned sp + -160 - pd + 32); (pk + 4, pk + 8)])
    by (clear - FIMG LOSP LOBIG PADCASE PKHI; ut_fp_lia; exact I).
  assert (SHF : sh_fp [(f + 32, f + 40); (bv_unsigned sp + -160 - pd - 144, bv_unsigned sp + -160 - pd + 32); (pk + 4, pk + 8)])
    by (clear - FSHAD LOSP LOBIG PADCASE PKHI; sh_fp_lia).
  remember (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) as rsp eqn:RSPDEF.
  assert (RSPU : bv_unsigned rsp = bv_unsigned sp + -160 - pd) by (subst rsp; apply unsigned_lit; clear - LOSP LOBIG SPTOP PADCASE; lia).
  rewrite <- RSPU in BELOW, PAD.
  assert (PSAL8 : ps mod 8 = 0) by (clear - PSAL; Z.div_mod_to_equations; lia).
  assert (PKU : bv_unsigned (Z_to_bv 64 pk) = pk) by (apply unsigned_lit; clear - PKPOS PKLO LOSP SPTOP; lia).
  destruct (ps_fsplit _ f hj FAKE) as (HEAD & SLOT & TAIL). clear FAKE.
  assert (TABLEOUT : forall a, plh_fp (t_of nm pl1 pl2) B bks a ->
            outside [(f + 32, f + 40); (bv_unsigned sp + -160 - pd - 144, bv_unsigned sp + -160 - pd + 32); (pk + 4, pk + 8)] a).
  { intros a [INT | [INB | (nd & NIN & INN)]]; cbn [outside].
    - clear - INT TABLEFAKE TABLELO LOSP PADCASE PKTABLE. lia.
    - clear - INB BFAKE BLO LOSP PADCASE PKB. lia.
    - destruct (NODES nd NIN) as (_ & _ & NLO & NFAKE & NPK). clear - INN NLO NFAKE NPK LOSP PADCASE. lia. }
  (* FSHAD served SHF; TABLEFAKE, PKTABLE, BFAKE and PKB served TABLEOUT; PSTABLE is never used. Clearing these six disjunctions keeps them out of every later lia *)
  clear FSHAD PSTABLE PKTABLE PKB TABLEFAKE BFAKE.
  (* the stores go through s1, the realigned frame base: give them a chunk based there *)
  destruct PADCASE as [PD | PD];
    [ assert (LOCAL : rw_cells asegs m (bv_unsigned rsp)
        [CB 56 j; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
        by (rewrite RSPU, PD, Z.sub_0_r; exact SAVED)
    | destruct (stk_carve asegs m (bv_unsigned rsp) (bv_unsigned sp + -160) 16 PAD ltac:(lia)) as [_ (pad & PADC)];
      replace (bv_unsigned sp + -160 - Z.of_nat 16) with (bv_unsigned rsp) in PADC by lia;
      assert (LOCAL : rw_cells asegs m (bv_unsigned rsp)
        [CB 16 pad; CB 56 j; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
        by (apply (proj2 (rw_cells_app m _ [CB 16 pad] _)); split; [exact PADC |];
            cbn [cells_size csize Nat.add];
            replace (bv_unsigned rsp + Z.of_nat 16) with (bv_unsigned sp + -160) by lia; exact SAVED);
      clear PADC ].
  all: clear SAVED.
  all: destruct nm; unfold nmz, t_of, off_idx in *.
  (* ossl_lib_ctx_get_data (ctx, 3) gives the store ps *)
  all: do 3 zstep.
  all: call (gd3_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo ps); try (solve [ eassumption | lia | reflexivity
                 | rewrite PKU; (eassumption || lia)
                 | rewrite RSPU; Z.div_mod_to_equations; lia
                 | eapply plh_rep_munch; [exact TABLE | exact MU | exact TABLEOUT]
                 | eapply acc_munch_sh; [eassumption | exact MU | exact SHF | lia | lia]
                 | eapply ut_munch; [exact UNT | exact MU | exact UTF]
                 | eapply acc_sub; [eapply acc_munch_sh; [exact CALLEEACC | exact MU | exact SHF | lia | lia] | lia | lia]
                 | eapply acc_sub; [apply ps_acc16; [exact FALIGN | exact FPOS | exact FAKESH] | lia | lia]
                 | intros nd NIN; destruct (NODES nd NIN) as (NACC & NPOS & NLO & _);
                   split; [eapply acc_munch_sh; [exact NACC | exact MU | exact SHF | lia | lia] | lia] ]).
  all: rename POST into BELOW.
  (* ps is not NULL; the shadow checks on the selected table field and on ps->lock pass *)
  all: repeat zstep; if_false_by (ubs_eqb0_false_lit ps ltac:(lia)).
  all: repeat zstep; first [if_true | if_false].
  all: repeat zstep; if_false.
  all: repeat zstep; if_false.
  (* CRYPTO_THREAD_read_lock (ps->lock) *)
  all: do 2 zstep.
  all: call (T_read_lock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); try (solve [ eassumption | lia | reflexivity
                 | rewrite PKU; (eassumption || lia)
                 | rewrite RSPU; Z.div_mod_to_equations; lia
                 | eapply plh_rep_munch; [exact TABLE | exact MU | exact TABLEOUT]
                 | eapply acc_munch_sh; [eassumption | exact MU | exact SHF | lia | lia]
                 | eapply ut_munch; [exact UNT | exact MU | exact UTF]
                 | eapply acc_sub; [eapply acc_munch_sh; [exact CALLEEACC | exact MU | exact SHF | lia | lia] | lia | lia]
                 | eapply acc_sub; [apply ps_acc16; [exact FALIGN | exact FPOS | exact FAKESH] | lia | lia]
                 | intros nd NIN; destruct (NODES nd NIN) as (NACC & NPOS & NLO & _);
                   split; [eapply acc_munch_sh; [exact NACC | exact MU | exact SHF | lia | lia] | lia] ]).
  all: rename PC into BELOW, POST into LOCK; rewrite PKU in LOCK; unfold mutex_cells in LOCK.
  all: repeat zstep; if_false.
  (* first lookup, under the read lock: a miss *)
  all: do 4 (zstep; fix_lit_store).
  all: lazymatch goal with T0 : plh_rep _ ?t _ _ _ |- _ => call (plh_retrieve_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t B items bks (f + 32) S lo str); try (solve [ eassumption | lia | reflexivity
                 | rewrite PKU; (eassumption || lia)
                 | rewrite RSPU; Z.div_mod_to_equations; lia
                 | eapply plh_rep_munch; [exact TABLE | exact MU | exact TABLEOUT]
                 | eapply acc_munch_sh; [eassumption | exact MU | exact SHF | lia | lia]
                 | eapply ut_munch; [exact UNT | exact MU | exact UTF]
                 | eapply acc_sub; [eapply acc_munch_sh; [exact CALLEEACC | exact MU | exact SHF | lia | lia] | lia | lia]
                 | eapply acc_sub; [apply ps_acc16; [exact FALIGN | exact FPOS | exact FAKESH] | lia | lia]
                 | intros nd NIN; destruct (NODES nd NIN) as (NACC & NPOS & NLO & _);
                   split; [eapply acc_munch_sh; [exact NACC | exact MU | exact SHF | lia | lia] | lia] ]) end.
  all: rename PC into BELOW, POST into TABLE1.
  all: repeat zstep; if_true.
  all: repeat zstep; if_false.
  all: repeat zstep; if_false.
  (* CRYPTO_THREAD_unlock, then CRYPTO_THREAD_write_lock *)
  all: do 2 zstep.
  all: call (T_unlock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); try (solve [ eassumption | lia | reflexivity
                 | rewrite PKU; (eassumption || lia)
                 | rewrite RSPU; Z.div_mod_to_equations; lia
                 | eapply plh_rep_munch; [exact TABLE | exact MU | exact TABLEOUT]
                 | eapply acc_munch_sh; [eassumption | exact MU | exact SHF | lia | lia]
                 | eapply ut_munch; [exact UNT | exact MU | exact UTF]
                 | eapply acc_sub; [eapply acc_munch_sh; [exact CALLEEACC | exact MU | exact SHF | lia | lia] | lia | lia]
                 | eapply acc_sub; [apply ps_acc16; [exact FALIGN | exact FPOS | exact FAKESH] | lia | lia]
                 | intros nd NIN; destruct (NODES nd NIN) as (NACC & NPOS & NLO & _);
                   split; [eapply acc_munch_sh; [exact NACC | exact MU | exact SHF | lia | lia] | lia] ]).
  all: rename PC into BELOW, POST into LOCK; rewrite PKU in LOCK; unfold mutex_cells in LOCK.
  all: repeat zstep; if_false.
  all: do 2 zstep.
  all: call (T_write_lock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); try (solve [ eassumption | lia | reflexivity
                 | rewrite PKU; (eassumption || lia)
                 | rewrite RSPU; Z.div_mod_to_equations; lia
                 | eapply plh_rep_munch; [exact TABLE | exact MU | exact TABLEOUT]
                 | eapply acc_munch_sh; [eassumption | exact MU | exact SHF | lia | lia]
                 | eapply ut_munch; [exact UNT | exact MU | exact UTF]
                 | eapply acc_sub; [eapply acc_munch_sh; [exact CALLEEACC | exact MU | exact SHF | lia | lia] | lia | lia]
                 | eapply acc_sub; [apply ps_acc16; [exact FALIGN | exact FPOS | exact FAKESH] | lia | lia]
                 | intros nd NIN; destruct (NODES nd NIN) as (NACC & NPOS & NLO & _);
                   split; [eapply acc_munch_sh; [exact NACC | exact MU | exact SHF | lia | lia] | lia] ]).
  all: rename PC into BELOW, POST into LOCK; rewrite PKU in LOCK; unfold mutex_cells in LOCK.
  all: repeat zstep; if_false.
  (* the table index goes to the frame slot at s1 + 8; then the second lookup, a miss again *)
  all: repeat zstep; first [if_true | if_false].
  all: repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
         tryif constr_eq p 2101192 then fail else (zstep; fix_lit_store) end).
  all: lazymatch goal with T0 : plh_rep _ ?t _ _ _ |- _ => call (plh_retrieve_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t B items bks (f + 32) S lo str); try (solve [ eassumption | lia | reflexivity
                 | rewrite PKU; (eassumption || lia)
                 | rewrite RSPU; Z.div_mod_to_equations; lia
                 | eapply plh_rep_munch; [exact TABLE | exact MU | exact TABLEOUT]
                 | eapply acc_munch_sh; [eassumption | exact MU | exact SHF | lia | lia]
                 | eapply ut_munch; [exact UNT | exact MU | exact UTF]
                 | eapply acc_sub; [eapply acc_munch_sh; [exact CALLEEACC | exact MU | exact SHF | lia | lia] | lia | lia]
                 | eapply acc_sub; [apply ps_acc16; [exact FALIGN | exact FPOS | exact FAKESH] | lia | lia]
                 | intros nd NIN; destruct (NODES nd NIN) as (NACC & NPOS & NLO & _);
                   split; [eapply acc_munch_sh; [exact NACC | exact MU | exact SHF | lia | lia] | lia] ]) end.
  all: rename PC into BELOW, POST into TABLE2.
  all: repeat zstep; if_false.
  (* a0 := S, the string held in s5; jump to strlen *)
  all: do 2 zstep.
  all: apply evt_done.
  (* rebuild the pieces ps_w1b_post names *)
  all: pose proof (ps_fjoin _ _ _ _ _ HEAD SLOT TAIL) as FAKEC.
  all: pose proof (rw_cells_tail _ _ _ _ LOCAL) as AT8; cbn [csize] in AT8.
  all: pose proof (rw_cells_head _ _ _ _ AT8) as OFFC.
  all: pose proof (rw_cells_tail _ _ _ _ AT8) as AT16; cbn [csize] in AT16.
  all: pose proof (rw_cells_head _ _ _ _ AT16) as NMC.
  all: pose proof (rw_cells_tail _ _ _ _ AT16) as AT24; cbn [csize] in AT24.
  all: pose proof (rw_cells_head _ _ _ _ AT24) as TC.
  all: first
       [ lazymatch type of LOCAL with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 24 ?b4 :: ?rest) =>
           pose proof (rw_cells_merge asegs _ _ [] [c0; c1; c2; c3; CB 24 b4] rest LOCAL) as FRAME end
       | lazymatch type of AT16 with rw_cells _ _ _ (?c0 :: ?c1 :: CB 40 ?b2 :: ?rest) =>
           pose proof (rw_cells_merge asegs _ _ [] [c0; c1; CB 40 b2] rest AT16) as FRAME end ].
  all: cbn [app cells_size csize Nat.add] in FRAME.
  all: lazymatch type of FRAME with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -160) in FRAME by lia end.
  all: lazymatch type of OFFC with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -160 - pd + 8) in OFFC by lia end.
  all: lazymatch type of NMC with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -160 - pd + 16) in NMC by lia end.
  all: lazymatch type of TC with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -160 - pd + 24) in TC by lia end.
  all: rewrite RSPU in PAD, BELOW.
  all: do 18 eexists; split; [reflexivity |].
  all: repeat match goal with |- _ /\ _ => split end.
  all: first [eassumption | eapply plh_rep_munch; [exact TABLE | exact MU | exact TABLEOUT]].
Qed.
