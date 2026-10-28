(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_leaves R_unwind_defs R_unwindimpl R_depot_defs R_asan_defs R_prim_kit R_intalloc R_asan_malloc R_deallocate R_asan_free R_asan_malloc_k R_asan_free_k RT_iface RT_state RT_unwindk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition free_tr_shape (cg : cgraph) (tr : list Z) : Prop := uw_tr_shape cg e_free PC_FREE tr.

Lemma free_tr_shape_main : forall cg tr, free_tr_shape cg tr ->
  In tr (T_MAIN cg) /\ (1 <= length tr <= 30)%nat /\ Forall (fun x => 0 <= x < 2 ^ 64) tr.
Proof. intros cg tr H. exact (uw_tr_shape_main tr H). Qed.
Arguments free_tr_shape_main {cg} tr _.

Lemma free_tr_shape_head : forall cg tr, free_tr_shape cg tr -> exists rest, tr = free_pc :: rest.
Proof.
  intros cg tr (_ & _ & [-> | [(ra & _ & ->) | (ch & r & t & _ & _ & _ & ->)]]); eexists; reflexivity.
Qed.
Arguments free_tr_shape_head {cg} tr _.

Lemma eps_malloc : In (e_malloc, PC_MALLOC) ALLOC_EPS. Proof. left; reflexivity. Qed.
Lemma eps_free : In (e_free, PC_FREE) ALLOC_EPS. Proof. right; left; reflexivity. Qed.

(* [comment removed for export] *)
Lemma malloc_front_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (n TCX T top bot lo : Z) (cg : cgraph),
  cg_wf cg ALLOC_EPS ALLOC_RAS N_TR ->
  (1 <= n <= 2^31)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2288)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp <= 2^63)%Z ->
  (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  unwind_ok cg e_malloc m ra s0 sp -> (4096 <= top)%Z -> (top <= 2 ^ 63)%Z ->
  rw_cells asegs m 0x5a4598 [C8 (Z_to_bv 64 0x6fc5e0)] ->
  rw_cells asegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
  rw_cells asegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells asegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x6fc5e0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbc6000 <= T)%Z ->
  (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  exists tr, (1 <= length tr <= 30)%nat /\ In tr (T_MAIN cg)
    /\ evt asegs (malloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n T lo tr m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 wrap_malloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until cg. intros WF Hn ST HLO HLOH HSP Hbt Htop UWOK Ht1 Ht2 G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl HT0 HT HTl HTT SC UW MI.
  destruct (unwind_ok_trace cg e_malloc PC_MALLOC [(T + 3168, T + 3169); (bv_unsigned sp - 2288, bv_unsigned sp)] m ra s0 sp bot top
              eps_malloc WF Ht1 Ht2) as (ch & tr & CCH & HTR & HS); [|exact UWOK|].
  { repeat constructor; cbn [snd]; lia. }
  destruct (uw_tr_shape_main tr HS) as (Htr & Htrl & _).
  exists tr. split; [exact Htrl|]. split; [exact Htr|].
  change PC_MALLOC with malloc_pc in HTR.
  exact (malloc_Ak_spec ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n
           TCX T top bot lo ch tr Hn ST HLO HLOH HSP Hbt Htop CCH HTR G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXl HT0 HT HTl HTT SC UW MI).
Qed.

(* [comment removed for export] *)
Lemma free_front_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p TCX T top bot lo : Z) (b : bool) (cg : cgraph),
  cg_wf cg ALLOC_EPS ALLOC_RAS N_TR ->
  (0 <= p < 2^47)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2288)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  unwind_ok cg e_free m ra s0 sp -> (4096 <= top)%Z -> (top <= 2 ^ 63)%Z ->
  ia_state b m ->
  rw_cells asegs m 0x5a4598 [C8 (Z_to_bv 64 0x6fc5e0)] ->
  rw_cells asegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x6fc5e0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= 0x10000 \/ 0xbc6000 <= TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
  (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbc6000 <= T)%Z -> (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  exists tr, free_tr_shape cg tr
    /\ evt asegs (free_pre_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p T lo tr m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 wrap_free_entry) fc None m (seg_rom asegs)).
Proof.
  intros until cg. intros WF Hp ST HLO HLOH HSP Hbt Htop UWOK Ht1 Ht2 IS G60 GCF AI MCS PSC FUM TC HTCX HTCXi HTCXl HT0 HT HTl HTT SC UW MI.
  destruct (unwind_ok_trace cg e_free PC_FREE [(T + 3168, T + 3169); (7325128, 7325132); (6741312, 7269744); (bv_unsigned sp - 2288, bv_unsigned sp)] m ra s0 sp bot top
              eps_free WF Ht1 Ht2) as (ch & tr & CCH & HTR & HS); [|exact UWOK|].
  { unfold kHighShadowEnd in HLOH. repeat constructor; cbn [snd]; lia. }
  exists tr. split; [exact HS|].
  change PC_FREE with free_pc in HTR.
  exact (free_prek_spec ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p
           TCX T top bot lo ch b tr Hp ST HLO HLOH HSP Hbt Htop CCH HTR IS G60 GCF AI MCS PSC FUM TC HTCX HTCXi HTCXl HT0 HT HTl HTT SC UW MI).
Qed.

(* [comment removed for export] *)
Lemma free_null_front_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (TCX T top bot lo : Z) (b : bool) (cg : cgraph),
  cg_wf cg ALLOC_EPS ALLOC_RAS N_TR ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2288)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  unwind_ok cg e_free m ra s0 sp -> (4096 <= top)%Z -> (top <= 2 ^ 63)%Z ->
  ia_state b m ->
  rw_cells asegs m 0x5a4598 [C8 (Z_to_bv 64 0x6fc5e0)] ->
  rw_cells asegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0x6fc5e0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= 0x10000 \/ 0xbc6000 <= TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
  (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0xbc6000 <= T)%Z -> (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  evt asegs (free_null_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 wrap_free_entry) fc None m (seg_rom asegs)).
Proof.
  intros until cg. intros WF ST HLO HLOH HSP Hbt Htop UWOK Ht1 Ht2 IS G60 GCF AI MCS PSC FUM TC HTCX HTCXi HTCXl HT0 HT HTl HTT SC UW MI.
  destruct (free_front_spec ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m 0
              TCX T top bot lo b cg WF ltac:(lia) ST HLO HLOH HSP Hbt Htop UWOK Ht1 Ht2 IS G60 GCF AI MCS PSC FUM TC HTCX HTCXi HTCXl
              HT0 HT HTl HTT SC UW MI) as (tr & SH & W).
  destruct (free_tr_shape_main tr SH) as (_ & LT & _).
  exact (free_null_tail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m T lo tr _ HLO HLOH HSP HT0 HTl ltac:(lia) W).
Qed.
