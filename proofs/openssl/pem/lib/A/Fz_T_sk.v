(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_G_CRYPTO_calloc Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Definition e_sk_reserve : Z := 0x1fa5e0.
Definition e_sk_insert : Z := 0x1faa5c.
Definition e_sk_push : Z := 0x1fb7f4.
Definition SITE_skr_calloc : Z := 0x1fa6e0.
Definition SITE_ski_reserve : Z := 0x1fab44.
Definition SK_FILE : Z := 0x495a0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition sk_cells (num pad data sorted nalloc comp cmpt freet copyt : word) : list cell :=
  [C4 num; C4 pad; C8 data; C4 sorted; C4 nalloc; C8 comp; C8 cmpt; C8 freet; C8 copyt].

(* [comment removed for export] *)
Lemma skr_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A : Z) (pad srt nalloc comp cmpt freet copyt : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo ->
  rw_cells asegs m A (sk_cells z64 pad z64 srt nalloc comp cmpt freet copyt) -> acc asegs m A 56 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (j : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_skr_calloc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 194) a4 a5 a6 a7
                    (Z_to_bv 64 (A + 8)) (Z_to_bv 64 4) s4 (Z_to_bv 64 (Z.shiftr (A + 8) 3 + SHB)) (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_CRYPTO_calloc) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ stk asegs m' lo (bv_unsigned sp + -80) /\ rw_cells asegs m' A (sk_cells z64 pad z64 srt nalloc comp cmpt freet copyt))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 1) z64 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sk_reserve) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A pad srt nalloc comp cmpt freet copyt
    heap_a align_a a_below sk_at acc_a img_ut shb_cell stack lo_heap lo_frame sp_top inv.
  unfold sk_cells in sk_at. unfold g_shadow_memory_dynamic_address, SHB in shb_cell.
  assert (fp_m : munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m) by (intros x _; reflexivity).
  assert (wm_m : wmono asegs m m) by (intros x hx; exact hx).
  assert (ut_w : ut_fp [(bv_unsigned sp - 80, bv_unsigned sp)]) by ut_fp_lia.
  assert (sh_w : sh_fp [(bv_unsigned sp - 80, bv_unsigned sp)]) by sh_fp_lia.
  th_frame 80%nat [8;8;8;8;8;8;8;8;8;8]%nat stack.
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 2102656) _ _ _ _) => fail
          | _ => first [zstep | if_false | if_true]
          end).
  finish. eassumption.
Qed.

(* [comment removed for export] *)
Lemma skr_w1 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A D : Z) (pad srt nalloc comp cmpt freet copyt : word) (j : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo -> rw_cells asegs m A (sk_cells z64 pad z64 srt nalloc comp cmpt freet copyt) -> acc asegs m A 56 ->
  0x10007fff8000 <= D -> D + 32 <= lo ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -80) [CB 8 j; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -80) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' : word) (m' : mem),
       ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(A + 8, A + 16); (A + 20, A + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' A (sk_cells z64 pad (Z_to_bv 64 D) srt (Z_to_bv 64 4) comp cmpt freet copyt))
    (MS (mkR (Z_to_bv 64 SITE_skr_calloc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 (A + 8)) (Z_to_bv 64 4) s4 (Z_to_bv 64 (Z.shiftr (A + 8) 3 + SHB)) (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_skr_calloc) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A D pad srt nalloc comp cmpt freet copyt j
    rav s0v s1v s2v s3v s4v s5v s6v s7v heap_a align_a a_below sk_at acc_a heap_d d_below img_ut shb_cell saved stack lo_heap lo_frame sp_top inv.
  unfold sk_cells in sk_at. unfold SITE_skr_calloc, SHB.
  assert (fp_m : munch [(A + 8, A + 16); (A + 20, A + 24)] m m) by (intros x _; reflexivity).
  assert (wm_m : wmono asegs m m) by (intros x hx; exact hx).
  assert (sh_w : sh_fp [(A + 8, A + 16); (A + 20, A + 24)]) by sh_fp_lia.
  repeat first [zstep | if_false | if_true | (unfold_cond; zsimp; first [if_false | if_true])].
  th_release saved (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Lemma ski_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A : Z) (pad nalloc comp cmpt freet copyt : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo ->
  rw_cells asegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) -> acc asegs m A 56 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (j : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_ski_reserve) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 1) z64 a3 a4 a5 a6 a7
                    z64 s3 val s5 s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_sk_reserve) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -112) [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ stk asegs m' lo (bv_unsigned sp + -112) /\ rw_cells asegs m' A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) val z64 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sk_insert) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val F fc m lo A pad nalloc comp cmpt freet copyt
    heap_a align_a a_below sk_at acc_a img_ut shb_cell stack lo_heap lo_frame sp_top inv.
  unfold sk_cells in sk_at. unfold g_shadow_memory_dynamic_address, SHB in shb_cell.
  assert (fp_m : munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m) by (intros x _; reflexivity).
  assert (wm_m : wmono asegs m m) by (intros x hx; exact hx).
  assert (ut_w : ut_fp [(bv_unsigned sp - 112, bv_unsigned sp)]) by ut_fp_lia.
  assert (sh_w : sh_fp [(bv_unsigned sp - 112, bv_unsigned sp)]) by sh_fp_lia.
  th_frame 112%nat [8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat stack.
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 2074080) _ _ _ _) => fail
          | _ => first [zstep | if_false | if_true | (unfold_cond; zsimp; first [if_false | if_true])]
          end).
  finish. eassumption.
Qed.

(* [comment removed for export] *)
Lemma ski_w1 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A D : Z) (pad comp cmpt freet copyt : word) (j : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo -> rw_cells asegs m A (sk_cells z64 pad (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) comp cmpt freet copyt) -> acc asegs m A 56 ->
  0x10007fff8000 <= D -> D mod 8 = 0 -> D + 32 <= lo -> rw_cells asegs m D [C8 z64; CB 24 (zeros 24)] -> acc asegs m D 32 -> (A + 56 <= D \/ D + 32 <= A) ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -112) [CB 8 j; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -112) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' a2' a3' a4' : word) (m' : mem),
       ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(A, A + 4); (D, D + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' A (sk_cells (Z_to_bv 64 1) pad (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) comp cmpt freet copyt)
       /\ rw_cells asegs m' D [C8 val; CB 24 (zeros 24)])
    (MS (mkR (Z_to_bv 64 SITE_ski_reserve) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
            z64 s3 val s5 s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ski_reserve) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s9 s10 s11 t3 t4 t5 t6 val F fc m lo A D pad comp cmpt freet copyt j
    rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
    heap_a align_a a_below sk_at acc_a heap_d align_d d_below d_at acc_d apart img_ut shb_cell saved stack lo_heap lo_frame sp_top inv.
  unfold sk_cells in sk_at. unfold SITE_ski_reserve, SHB.
  assert (fp_m : munch [(A, A + 4); (D, D + 8)] m m) by (intros x _; reflexivity).
  assert (wm_m : wmono asegs m m) by (intros x hx; exact hx).
  assert (sh_w : sh_fp [(A, A + 4); (D, D + 8)]) by sh_fp_lia.
  repeat first [zstep; rewrite ?t_sx32_small by lia | if_false | if_true | (unfold_cond; zsimp; first [if_false | if_true])].
  th_release saved (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Lemma skp_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A : Z) (pad nalloc comp cmpt freet copyt : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo ->
  rw_cells asegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) -> acc asegs m A 56 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a4' : word) (m' : mem),
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) val z64 (Z_to_bv 64 (Z.shiftr A 3)) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_sk_insert) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) val a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sk_push) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val F fc m lo A pad nalloc comp cmpt freet copyt
    heap_a align_a a_below sk_at acc_a img_ut shb_cell stack lo_heap lo_frame sp_top inv.
  unfold sk_cells in sk_at. unfold g_shadow_memory_dynamic_address, SHB in shb_cell.
  assert (fp_m : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m) by (intros x _; reflexivity).
  assert (wm_m : wmono asegs m m) by (intros x hx; exact hx).
  assert (ut_w : ut_fp [(bv_unsigned sp - 16, bv_unsigned sp)]) by ut_fp_lia.
  assert (sh_w : sh_fp [(bv_unsigned sp - 16, bv_unsigned sp)]) by sh_fp_lia.
  th_frame 16%nat [8;8]%nat stack.
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 2075228) _ _ _ _) => fail
          | _ => first [zstep | if_false | if_true | (unfold_cond; zsimp; first [if_false | if_true])]
          end).
  lazymatch goal with saved : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release saved (bv_unsigned sp) end.
  finish.
Qed.

Section CSk.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CALLOC : CRYPTO_calloc_stmt RT.

Definition SKR_SITES : list (Z * Z) := [(SITE_skr_calloc, e_sk_reserve); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition SKR_CALLS : list (Z * Z) := [(SITE_skr_calloc, e_CRYPTO_calloc); (SITE_skr_calloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].
Definition SKI_SITES : list (Z * Z) := (SITE_ski_reserve, e_sk_insert) :: SKR_SITES.
Definition SKI_CALLS : list (Z * Z) := (SITE_ski_reserve, e_sk_reserve) :: SKR_CALLS.

(* [comment removed for export] *)
Definition sk_first_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z)
    (canary : word) (A : Z) (num pad comp cmpt freet copyt w : word) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (D : Z),
       ASTA RT Σ' PMc (fun ms => exists m' : mem,
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (A, A + 56)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' A (sk_cells num pad (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) comp cmpt freet copyt)
           /\ rw_cells asegs m' D [C8 w; CB 24 (zeros 24)]) c
       /\ rt_live RT Σ' = (D, 32) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ 0 < D /\ D mod 16 = 0 /\ D + 32 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ.

(* [comment removed for export] *)
Definition sk_reserve_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (A : Z) (pad nalloc comp cmpt freet copyt : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 1 -> a2 = z64 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 368 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_sk_reserve (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) SKR_SITES SKR_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  In (A, 56) (rt_live RT Σ) -> A mod 8 = 0 -> rw_cells asegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sk_reserve m)))
    (sk_first_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary A z64 pad comp cmpt freet copyt z64).

Theorem sk_reserve_first_cps : sk_reserve_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    A pad nalloc comp cmpt freet copyt only_fd mstab tp_is a0_is a1_is a2_is art inv call room ctx unw graph live_room credit env a_live a_al cells.
  subst tp a0 a1 a2. intros T c start then_k.
  destruct call as (stack & win_lo & lo_room & sp_room & sp_al).
  pose proof (af_sp0_win RT AF Σ m art) as sp0_hi.
  pose proof (af_live_range RT AF Σ m A 56 art a_live) as (_ & a_win & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m A 56 art a_live ltac:(lia)) as a_heap.
  pose proof (proj2 (af_acc_live RT AF Σ m A 56 art a_live)) as a_acc.
  destruct (af_client_consts RT AF Σ m art) as (_ & shb0 & _ & _ & ut0).
  assert (lo_heap : 0x10007fff8000 <= lo) by (unfold STACK_WIN in *; lia).
  assert (a_below : A + 56 <= lo) by lia.
  assert (sp_top : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  unfold RT_STACK in room, lo_room.
  (* entry of the function at e_sk_reserve to its call of e_CRYPTO_calloc *)
  pose proof (skr_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A
                pad (Z_to_bv 64 1) nalloc comp cmpt freet copyt a_heap a_al a_below cells a_acc ut0 shb0 stack lo_heap ltac:(lia) sp_top inv)
    as walk0.
  cl_lift walk0 start c1 at_c1.
  destruct (ASTA_unpack RT Σ _ _ c1 at_c1) as (ms1 & (j1 & m1 & -> & mu1 & wm1 & inv1 & frame1 & stk1 & cells1) & here1). clear at_c1.
  assert (above1 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1).
  { apply (agree_of_munch _ m m1 _ mu1). intros x hx. cbn [outside]. split; [lia | exact I]. }
  assert (sp80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80)
    by (apply unsigned_lit; unfold USTACK_TOP, STACK_WIN in *; lia).
  pose proof (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 80 [] art ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) mu1
                ltac:(intros x out_x; exfalso; apply out_x; exact I) wm1) as art1.
  pose proof (cl_seg_pres RT AF Σ m m1 (bv_unsigned sp) 80 [] art ltac:(lia) ltac:(lia) mu1) as keep1.
  assert (link1 : rw_cells asegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip m1 (bv_unsigned sp + -80) [CB 8 j1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] frame1)
      as tail. cbn [cells_size csize Nat.add] in tail.
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -80 + Z.of_nat 64) by lia. exact tail. }
  destruct (cl_chain_call (rt_cg RT Σ) e_sk_reserve e_CRYPTO_calloc SITE_skr_calloc m m1 ra s0 sp (Z_to_bv 64 (bv_unsigned sp + -80)) outer
              ctx (proj1 graph _ ltac:(unfold SKR_SITES; cbn; tauto)) (proj2 graph _ ltac:(unfold SKR_CALLS; cbn; tauto)) unw
              above1 link1
              ltac:(rewrite sp80; lia) ltac:(unfold USTACK_TOP in *; lia)) as (ctx1 & unw1).
  assert (calloc_size : 1 <= bv_unsigned (Z_to_bv 64 4) * bv_unsigned (Z_to_bv 64 8) <= 67108864) by (rewrite !unsigned_lit by lia; lia).
  assert (call1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -80)) lo).
  { unfold call_ok. rewrite sp80. split; [exact stk1 |]. split; [exact win_lo |]. split; [unfold RT_STACK; lia |].
    split; [unfold USTACK_TOP in *; lia |]. clear - sp_al. Z.div_mod_to_equations. lia. }
  assert (ctx1' : cg_ctx (rt_cg RT Σ) e_CRYPTO_calloc (bv_unsigned (Z_to_bv 64 SITE_skr_calloc) :: bv_unsigned ra :: outer))
    by (rewrite unsigned_lit by (unfold SITE_skr_calloc; lia); exact ctx1).
  assert (tail1 : In (bv_unsigned (Z_to_bv 64 SITE_skr_calloc), e_CRYPTO_zalloc) (cg_call (rt_cg RT Σ)))
    by (rewrite unsigned_lit by (unfold SITE_skr_calloc; lia); apply (proj2 graph); unfold SKR_CALLS; cbn; tauto).
  assert (graph1 : cg_has (rt_cg RT Σ) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                     [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (apply (cg_has_weaken _ _ _ _ _ graph); vm_compute; reflexivity).
  assert (credit1 : mcost (bv_unsigned (Z_to_bv 64 4) * bv_unsigned (Z_to_bv 64 8)) <= rt_credit RT Σ)
    by (change (mcost (bv_unsigned (Z_to_bv 64 4) * bv_unsigned (Z_to_bv 64 8))) with 0; exact credit).
  assert (env1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary env mu1); cl_fp_lia).
  apply (cps_realizes asegs _ _ T c1
           (C_CALLOC Σ PMc (Z_to_bv 64 SITE_skr_calloc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 A)
              (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 194) a4 a5 a6 a7 (Z_to_bv 64 (A + 8)) (Z_to_bv 64 4) s4
              (Z_to_bv 64 (Z.shiftr (A + 8) 3 + SHB)) (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary
              only_fd mstab eq_refl calloc_size eq_refl art1 inv1 call1 ltac:(rewrite sp80; unfold RT_STACK; lia) ctx1' unw1 tail1 graph1
              live_room credit1 env1) here1).
  intros c2 (Σ2 & D & at_c2 & lv2 & fr2 & sp02 & cr2 & d_pos & d_al & d_top & cg2).
  change (bv_unsigned (Z_to_bv 64 4) * bv_unsigned (Z_to_bv 64 8)) with 32 in *.
  change (mcost 32) with 0 in cr2.
  destruct (ASTA_unpack RT Σ2 _ _ c2 at_c2) as (ms2 & (m2 & back2 & (art2 & inv2 & wm2 & stk2) & pres2 & env2 & wr2 & acc2 & zero2) & here2).
  clear at_c2.
  destruct back2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite (ret_pc_even SITE_skr_calloc) in here2 by (unfold SITE_skr_calloc; first [lia | reflexivity]).
  rewrite sp80 in stk2, pres2.
  assert (d_in : In (D, 32) (rt_live RT Σ2)) by (rewrite lv2; left; reflexivity).
  assert (a_in2 : In (A, 56) (rt_live RT Σ2)) by (rewrite lv2; right; exact a_live).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m2 D 32 art2 d_in ltac:(lia)) as d_heap.
  pose proof (af_live_range RT AF Σ2 m2 D 32 art2 d_in) as (_ & d_win & _). rewrite sp02 in d_win.
  pose proof (af_live_disj RT AF Σ2 m2 D 32 A 56 [] (rt_live RT Σ) art2 lv2 a_live) as d_apart.
  pose proof (proj2 (af_acc_live RT AF Σ2 m2 A 56 art2 a_in2)) as a_acc2.
  destruct (af_client_consts RT AF Σ2 m2 art2) as (_ & shb2 & _ & _ & ut2).
  assert (cells2 : rw_cells asegs m2 A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt)).
  { apply (rw_cells_agree asegs m1 m2 _ _ cells1); [| exact wm2]. intros x hx. unfold sk_cells in hx. cbn [cells_size csize Nat.add] in hx.
    apply pres2; [apply (acl_live _ _ _ A 56); [exact a_live | lia] |].
    cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (frame2 : rw_cells asegs m2 (bv_unsigned sp + -80) [CB 8 j1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m2 _ _ frame1); [| exact wm2]. intros x hx. cbn [cells_size csize Nat.add] in hx.
    apply pres2; [apply acl_stack; unfold USTACK_TOP in *; lia |].
    cbn [outside]. unfold G_ALLOW_CUST, STACK_WIN in *. split; [lia | exact I]. }
  (* return from e_CRYPTO_calloc to the return of the function at e_sk_reserve *)
  pose proof (skr_w1 sp gp (Z_to_bv 64 TP_A) u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 s4 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo A D
                pad (Z_to_bv 64 1) nalloc comp cmpt freet copyt j1 ra s0 s1 s2 s3 s4 s5 s6 s7
                a_heap a_al a_below cells2 a_acc2 d_heap ltac:(unfold STACK_WIN in *; lia) ut2 shb2 frame2 stk2 lo_heap ltac:(lia) sp_top inv2)
    as walk1.
  cl_lift walk1 here2 c3 at_c3.
  destruct (ASTA_unpack RT Σ2 _ _ c3 at_c3) as (ms3 & (a1' & m3 & -> & mu3 & wm3 & inv3 & stk3 & cells3) & here3). clear at_c3.
  assert (zcells2 : rw_cells asegs m2 D [C8 z64; CB 24 (zeros 24)]).
  { apply (rw_cells_recast m2 D [CB 32 (repeat (Z_to_bv 8 0) 32)]); [| cbn; repeat split; reflexivity | reflexivity].
    split; [split; [cbn; split; [reflexivity | exact I] | exact zero2] | exact wr2]. }
  assert (zcells3 : rw_cells asegs m3 D [C8 z64; CB 24 (zeros 24)]).
  { apply (rw_cells_agree asegs m2 m3 _ _ zcells2); [| exact wm3]. intros x hx. cbn [cells_size csize Nat.add] in hx.
    apply mu3. cbn [outside]. repeat split; try exact I; lia. }
  assert (art3 : ART RT Σ2 m3).
  { apply (af_frame RT AF Σ2 m2 m3 (bv_unsigned sp) art2 ltac:(rewrite sp02; lia)); [| exact wm3].
    intros x not_client. apply mu3. cbn [outside].
    assert (off_a : ~ (A <= bv_unsigned x < A + 56)) by (intros hx; apply not_client; exact (acl_live _ _ _ A 56 _ a_in2 hx)).
    repeat split; try exact I; lia. }
  apply then_k. exists Σ2, D.
  assert (cr2' : rt_credit RT Σ2 = rt_credit RT Σ) by (rewrite cr2; lia).
  refine (conj _ (conj lv2 (conj fr2 (conj sp02 (conj cr2' (conj d_pos (conj d_al (conj d_top cg2)))))))).
  apply (ASTA_conseq RT Σ2 PMc _ _ c3 here3). intros ms <-. exists m3.
  split; [exists u0, u1, u2, a1', v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, F2, fc2; reflexivity |].
  split; [exact (conj art3 (conj inv3 (conj (wmono_trans asegs _ _ _ wm1 (wmono_trans asegs _ _ _ wm2 wm3)) stk3))) |].
  split.
  { intros x client off_w. cbn [outside] in off_w. destruct off_w as (off_g & off_a & _).
    rewrite (mu3 x ltac:(cbn [outside]; repeat split; try exact I; lia)).
    rewrite (pres2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ client); [exact (fun e he => he) | exact (fun e he => he) | lia])
                     ltac:(cbn [outside]; split; [exact off_g | exact I])).
    exact (keep1 x client I). }
  split; [apply (cl_env_seg _ m2 m3 _ canary env2 mu3); cl_fp_lia |].
  split; [exact cells3 | exact zcells3].
Qed.

(* [comment removed for export] *)
Definition sk_insert_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (A : Z) (pad nalloc comp cmpt freet copyt : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 A -> a2 = z64 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 480 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_sk_insert (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) SKI_SITES SKI_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  In (A, 56) (rt_live RT Σ) -> A mod 8 = 0 -> rw_cells asegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sk_insert m)))
    (sk_first_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary A (Z_to_bv 64 1) pad comp cmpt freet copyt a1).


Theorem sk_insert_first_cps : sk_insert_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 val a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    A pad nalloc comp cmpt freet copyt only_fd mstab tp_is a0_is a2_is art inv call room ctx unw graph live_room credit env a_live a_al cells.
  subst tp a0 a2. intros T c start then_k.
  destruct call as (stack & win_lo & lo_room & sp_room & sp_al).
  unfold RT_STACK in room, lo_room.
  pose proof (af_sp0_win RT AF Σ m art) as sp0_hi.
  pose proof (af_live_range RT AF Σ m A 56 art a_live) as (_ & a_win & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m A 56 art a_live ltac:(lia)) as a_heap.
  pose proof (proj2 (af_acc_live RT AF Σ m A 56 art a_live)) as a_acc.
  destruct (af_client_consts RT AF Σ m art) as (_ & shb0 & _ & _ & ut0).
  assert (lo_heap : 0x10007fff8000 <= lo) by (unfold STACK_WIN in *; lia).
  assert (a_below : A + 56 <= lo) by lia.
  assert (sp_top : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  (* entry of OPENSSL_sk_insert to its call of sk_reserve *)
  pose proof (ski_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val F fc m lo A
                pad nalloc comp cmpt freet copyt a_heap a_al a_below cells a_acc ut0 shb0 stack lo_heap ltac:(lia) sp_top inv) as walk0.
  cl_lift walk0 start c1 at_c1.
  destruct (ASTA_unpack RT Σ _ _ c1 at_c1) as (ms1 & (j1 & m1 & -> & mu1 & wm1 & inv1 & frame1 & stk1 & cells1) & here1). clear at_c1.
  assert (sp112 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112)
    by (apply unsigned_lit; unfold USTACK_TOP, STACK_WIN in *; lia).
  assert (above1 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1).
  { apply (agree_of_munch _ m m1 _ mu1). intros x hx. cbn [outside]. split; [lia | exact I]. }
  pose proof (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 112 [] art ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) mu1
                ltac:(intros x out_x; exfalso; apply out_x; exact I) wm1) as art1.
  pose proof (cl_seg_pres RT AF Σ m m1 (bv_unsigned sp) 112 [] art ltac:(lia) ltac:(lia) mu1) as keep1.
  assert (link1 : rw_cells asegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip m1 (bv_unsigned sp + -112)
                  [CB 8 j1; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] frame1) as tail.
    cbn [cells_size csize Nat.add] in tail.
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -112 + Z.of_nat 96) by lia. exact tail. }
  destruct (cl_chain_call (rt_cg RT Σ) e_sk_insert e_sk_reserve SITE_ski_reserve m m1 ra s0 sp (Z_to_bv 64 (bv_unsigned sp + -112)) outer
              ctx (proj1 graph _ ltac:(unfold SKI_SITES; cbn; tauto)) (proj2 graph _ ltac:(unfold SKI_CALLS; cbn; tauto)) unw
              above1 link1 ltac:(rewrite sp112; lia) ltac:(unfold USTACK_TOP in *; lia)) as (ctx1 & unw1).
  assert (call1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -112)) lo).
  { unfold call_ok. rewrite sp112. split; [exact stk1 |]. split; [exact win_lo |]. split; [unfold RT_STACK; lia |].
    split; [unfold USTACK_TOP in *; lia |]. clear - sp_al. Z.div_mod_to_equations. lia. }
  assert (ctx1' : cg_ctx (rt_cg RT Σ) e_sk_reserve (bv_unsigned (Z_to_bv 64 SITE_ski_reserve) :: bv_unsigned ra :: outer))
    by (rewrite unsigned_lit by (unfold SITE_ski_reserve; lia); exact ctx1).
  assert (graph1 : cg_has (rt_cg RT Σ) SKR_SITES SKR_CALLS) by (apply (cg_has_weaken _ _ _ _ _ graph); vm_compute; reflexivity).
  assert (env1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary env mu1); cl_fp_lia).
  apply (cps_realizes asegs _ _ T c1
           (sk_reserve_first_cps Σ PMc (Z_to_bv 64 SITE_ski_reserve) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp
              (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 1) z64 a3 a4 a5 a6 a7 z64 s3 val s5 s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 SHB)
              s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary A pad nalloc comp cmpt freet copyt
              only_fd mstab eq_refl eq_refl eq_refl eq_refl art1 inv1 call1 ltac:(rewrite sp112; unfold RT_STACK; lia) ctx1' unw1 graph1
              live_room credit env1 a_live a_al cells1) here1).
  intros c2 (Σ2 & D & at_c2 & lv2 & fr2 & sp02 & cr2 & d_pos & d_al & d_top & cg2).
  destruct (ASTA_unpack RT Σ2 _ _ c2 at_c2) as (ms2 & (m2 & back2 & (art2 & inv2 & wm2 & stk2) & pres2 & env2 & cells2 & zcells2) & here2).
  clear at_c2.
  destruct back2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite (ret_pc_even SITE_ski_reserve) in here2 by (unfold SITE_ski_reserve; first [lia | reflexivity]).
  rewrite sp112 in stk2, pres2.
  assert (d_in : In (D, 32) (rt_live RT Σ2)) by (rewrite lv2; left; reflexivity).
  assert (a_in2 : In (A, 56) (rt_live RT Σ2)) by (rewrite lv2; right; exact a_live).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m2 D 32 art2 d_in ltac:(lia)) as d_heap.
  pose proof (af_live_range RT AF Σ2 m2 D 32 art2 d_in) as (_ & d_win & _). rewrite sp02 in d_win.
  pose proof (af_live_disj RT AF Σ2 m2 D 32 A 56 [] (rt_live RT Σ) art2 lv2 a_live) as d_apart.
  pose proof (proj2 (af_acc_live RT AF Σ2 m2 A 56 art2 a_in2)) as a_acc2.
  pose proof (proj2 (af_acc_live RT AF Σ2 m2 D 32 art2 d_in)) as d_acc2.
  destruct (af_client_consts RT AF Σ2 m2 art2) as (_ & shb2 & _ & _ & ut2).
  assert (frame2 : rw_cells asegs m2 (bv_unsigned sp + -112)
                     [CB 8 j1; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m1 m2 _ _ frame1); [| exact wm2]. intros x hx. cbn [cells_size csize Nat.add] in hx.
    apply pres2; [apply acl_stack; unfold USTACK_TOP in *; lia |].
    cbn [outside]. unfold G_ALLOW_CUST, STACK_WIN in *. repeat split; try exact I; lia. }
  (* return from sk_reserve to the return of OPENSSL_sk_insert *)
  pose proof (ski_w1 sp gp (Z_to_bv 64 TP_A) u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 s3 s5 s6 s9 s10 s11 u3 u4 u5 u6 val F2 fc2 m2 lo A D
                pad comp cmpt freet copyt j1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                a_heap a_al a_below cells2 a_acc2 d_heap ltac:(clear - d_al; Z.div_mod_to_equations; lia) ltac:(unfold STACK_WIN in *; lia)
                zcells2 d_acc2 (proj1 (or_comm _ _) d_apart) ut2 shb2 frame2 stk2 lo_heap ltac:(lia) sp_top inv2) as walk1.
  cl_lift walk1 here2 c3 at_c3.
  destruct (ASTA_unpack RT Σ2 _ _ c3 at_c3) as (ms3 & (b1 & b2 & b3 & b4 & m3 & -> & mu3 & wm3 & inv3 & stk3 & cells3 & dcells3) & here3).
  clear at_c3.
  assert (art3 : ART RT Σ2 m3).
  { apply (af_frame RT AF Σ2 m2 m3 (bv_unsigned sp) art2 ltac:(rewrite sp02; lia)); [| exact wm3].
    intros x not_client. apply mu3. cbn [outside].
    assert (off_a : ~ (A <= bv_unsigned x < A + 56)) by (intros hx; apply not_client; exact (acl_live _ _ _ A 56 _ a_in2 hx)).
    assert (off_d : ~ (D <= bv_unsigned x < D + 32)) by (intros hx; apply not_client; exact (acl_live _ _ _ D 32 _ d_in hx)).
    repeat split; try exact I; lia. }
  apply then_k. exists Σ2, D.
  refine (conj _ (conj lv2 (conj fr2 (conj sp02 (conj cr2 (conj d_pos (conj d_al (conj d_top cg2)))))))).
  apply (ASTA_conseq RT Σ2 PMc _ _ c3 here3). intros ms <-. exists m3.
  split; [exists u0, u1, u2, b1, b2, b3, b4, v5, v6, v7, u3, u4, u5, u6, F2, fc2; reflexivity |].
  split; [exact (conj art3 (conj inv3 (conj (wmono_trans asegs _ _ _ wm1 (wmono_trans asegs _ _ _ wm2 wm3)) stk3))) |].
  split.
  { intros x client off_w. pose proof off_w as off_w'. cbn [outside] in off_w'. destruct off_w' as (off_g & off_a & _).
    pose proof (newchunk_apart RT AF Σ Σ2 m2 D 32 (bv_unsigned sp) (bv_unsigned x) art2 lv2 fr2 sp02 ltac:(lia) ltac:(lia) client) as off_d.
    rewrite (mu3 x ltac:(cbn [outside]; repeat split; try exact I; lia)).
    rewrite (pres2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ client); [exact (fun e he => he) | exact (fun e he => he) | lia]) off_w).
    exact (keep1 x client I). }
  split; [apply (cl_env_seg _ m2 m3 _ canary env2 mu3); cl_fp_lia |].
  split; [exact cells3 | exact dcells3].
Qed.

(* [comment removed for export] *)
Definition sk_push_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (A : Z) (pad nalloc comp cmpt freet copyt : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 480 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_sk_push (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> In (bv_unsigned ra, e_sk_insert) (cg_call (rt_cg RT Σ)) ->
  cg_has (rt_cg RT Σ) SKI_SITES SKI_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  In (A, 56) (rt_live RT Σ) -> A mod 8 = 0 -> rw_cells asegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sk_push m)))
    (sk_first_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary A (Z_to_bv 64 1) pad comp cmpt freet copyt a1).

Theorem sk_push_first_cps : sk_push_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 val a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    A pad nalloc comp cmpt freet copyt only_fd mstab tp_is a0_is art inv call room ctx unw hop graph live_room credit env a_live a_al cells.
  subst tp a0. intros T c start then_k.
  destruct call as (stack & win_lo & lo_room & sp_room & sp_al).
  pose proof (af_sp0_win RT AF Σ m art) as sp0_hi.
  pose proof (af_live_range RT AF Σ m A 56 art a_live) as (_ & a_win & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m A 56 art a_live ltac:(lia)) as a_heap.
  pose proof (proj2 (af_acc_live RT AF Σ m A 56 art a_live)) as a_acc.
  destruct (af_client_consts RT AF Σ m art) as (_ & shb0 & _ & _ & ut0).
  assert (lo_heap : 0x10007fff8000 <= lo) by (unfold STACK_WIN in *; lia).
  assert (a_below : A + 56 <= lo) by lia.
  assert (sp_top : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  (* OPENSSL_sk_push reads the count and jumps into OPENSSL_sk_insert *)
  pose proof (skp_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val F fc m lo A
                pad nalloc comp cmpt freet copyt a_heap a_al a_below cells a_acc ut0 shb0 stack lo_heap ltac:(unfold RT_STACK in *; lia) sp_top inv)
    as walk0.
  cl_lift walk0 start c1 at_c1.
  destruct (ASTA_unpack RT Σ _ _ c1 at_c1) as (ms1 & (a4' & m1 & -> & mu1 & wm1 & inv1 & stk1 & cells1) & here1). clear at_c1.
  assert (above1 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1).
  { apply (agree_of_munch _ m m1 _ mu1). intros x hx. cbn [outside]. split; [lia | exact I]. }
  pose proof (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 16 [] art ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) mu1
                ltac:(intros x out_x; exfalso; apply out_x; exact I) wm1) as art1.
  pose proof (cl_seg_pres RT AF Σ m m1 (bv_unsigned sp) 16 [] art ltac:(unfold RT_STACK in *; lia) ltac:(lia) mu1) as keep1.
  assert (env1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary env mu1); unfold RT_STACK in *; cl_fp_lia).
  apply (cps_realizes asegs _ _ T c1
           (sk_insert_first_cps Σ PMc ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 A) val z64 (Z_to_bv 64 (Z.shiftr A 3)) a4' a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo outer lb canary A pad nalloc comp cmpt freet copyt
              only_fd mstab eq_refl eq_refl eq_refl art1 inv1 (conj stk1 (conj win_lo (conj lo_room (conj sp_room sp_al)))) room
              (conj hop (proj2 ctx)) (uw_chain_agree outer m m1 sp s0 unw above1) graph live_room credit env1 a_live a_al cells1) here1).
  intros c2 (Σ2 & D & at_c2 & rest). apply then_k. exists Σ2, D. split; [| exact rest].
  apply (ASTA_conseq RT Σ2 PMc _ _ c2 at_c2).
  intros ms (m2 & back2 & (art2 & inv2 & wm2 & stk2) & pres2 & tail2). exists m2.
  split; [exact back2 |]. split; [exact (conj art2 (conj inv2 (conj (wmono_trans asegs _ _ _ wm1 wm2) stk2))) |].
  split; [| exact tail2].
  apply (pres_fp_trans _ _ _ _ m m1 m2); [| exact pres2]. intros x client _. exact (keep1 x client I).
Qed.
End CSk.
