(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Th_mutex Fz_T_lock Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_realloc Fz_M_realloc_array Fz_G_CRYPTO_calloc Fz_T_sk Fz_I1_insw Fz_I1_insx Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_insw Fz_K_insert Fz_K_skw Fz_K_sk Fz_I2_ppis Fz_K_pstw Fz_K_pstw2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition PSTR_STK : Z := 0x2c0.

(* [comment removed for export] *)
Definition PSTR_SITES : list (Z * Z) :=
  [(SITE_ps_malloc, e_property_string); (SITE_ps_push, e_property_string); (SITE_ps_insert, e_property_string); (SITE_cm_malloc, e_CRYPTO_malloc)]
  ++ KI_SITES ++ SKI_SITES ++ KG_SITES.
Definition PSTR_CALLS : list (Z * Z) :=
  [(SITE_ps_malloc, e_CRYPTO_malloc); (SITE_ps_push, e_sk_push); (SITE_ps_push, e_sk_insert); (SITE_ps_insert, e_lh_insert); (SITE_cm_malloc, e_malloc)]
  ++ KI_CALLS ++ SKI_CALLS ++ KG_CALLS.

Lemma PSTR_in_PPI : incl PSTR_SITES PPI_SITES /\ incl PSTR_CALLS PPI_CALLS.
Proof.
  split; intros x Hx; unfold PSTR_SITES, PSTR_CALLS, KI_SITES, KI_CALLS, SKI_SITES, SKI_CALLS, SKR_SITES, SKR_CALLS, KG_SITES, KG_CALLS in Hx;
    cbn [app In] in Hx; unfold PPI_SITES, PPI_CALLS;
    repeat (destruct Hx as [<- | Hx]; [vm_compute; tauto|]); destruct Hx.
Qed.

(* [comment removed for export] *)
Definition rngs (L : list (Z * Z)) : list (Z * Z) := map (fun e => (fst e, fst e + snd e)) L.
Definition pstr_W (L : list (Z * Z)) : list (Z * Z) := (G_ALLOW_CUST, G_ALLOW_CUST + 1) :: rngs L.
(* [comment removed for export] *)
Definition pstr_L (nm : bool) (ps pk pl1 pl2 pq1 pq2 B : Z) (bks : list (list pnode)) : list (Z * Z) :=
  (ps, 48) :: (pk, 40) :: (q_of nm pq1 pq2, 56) :: plh_L (t_of nm pl1 pl2) B bks.

(* [comment removed for export] *)
Definition pstr_bks (bks : list (list pnode)) (str : list byte) (pnn : Z) : list (list pnode) :=
  lupd (Z.to_nat (lh_strhash str mod 8)) (nth (Z.to_nat (lh_strhash str mod 8)) bks [] ++ [(pnn, lh_strhash str)]) bks.

(* [comment removed for export] *)
Lemma pstr_bks_incl : forall lh B (bks : list (list pnode)) (str : list byte) pnn (L : list (Z * Z)),
  length bks = 16%nat -> incl (plh_L lh B bks) L -> incl (plh_L lh B (pstr_bks bks str pnn)) ((pnn, 24) :: L).
Proof.
  intros lh B bks str pnn L LEN HI x Hx. unfold plh_L, pstr_bks in *.
  destruct Hx as [<-|[<-|Hx]]; [right; apply HI; left; reflexivity| right; apply HI; right; left; reflexivity|].
  apply in_map_iff in Hx. destruct Hx as (n & <- & Hn).
  assert (LI : (Z.to_nat (lh_strhash str mod 8) < length bks)%nat) by (rewrite LEN; pose proof (Z.mod_pos_bound (lh_strhash str) 8 ltac:(lia)); lia).
  pose proof (concat_lupd bks _ (nth (Z.to_nat (lh_strhash str mod 8)) bks [] ++ [(pnn, lh_strhash str)]) LI) as P1.
  pose proof (concat_split_perm bks _ LI) as P2.
  apply (Permutation_in _ P1) in Hn. rewrite <- app_assoc in Hn. apply in_app_or in Hn. destruct Hn as [Hn|Hn].
  - right. apply HI. right; right. apply in_map_iff. exists n. split; [reflexivity|].
    apply (Permutation_in _ (Permutation_sym P2)). apply in_or_app. left. exact Hn.
  - cbn [app] in Hn. destruct Hn as [<-|Hn]; [left; reflexivity|]. right. apply HI. right; right. apply in_map_iff. exists n. split; [reflexivity|].
    apply (Permutation_in _ (Permutation_sym P2)). apply in_or_app. right. exact Hn.
Qed.

Section PstrStmts.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.

(* [comment removed for export] *)
Definition pstr_pre (Σ : rts RT) (PMc : Model -> Prop) (ra sp tp s0 a0 a1 a2 a3 : word) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
    (nm : bool) (S b sz : Z) (str slack : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) : Prop :=
  fdfs_only PMc /\ mat_stable PMc
  /\ a0 = Z_to_bv 64 PPI_CTX /\ a1 = Z_to_bv 64 (nmz nm) /\ a2 = Z_to_bv 64 1 /\ a3 = Z_to_bv 64 S /\ tp = Z_to_bv 64 0xba3ef0
  /\ ART RT Σ m /\ mem_inv asegs m /\ call_ok RT Σ m sp lo /\ lo + RT_STACK + PSTR_STK <= bv_unsigned sp
  /\ cg_ctx (rt_cg RT Σ) e_property_string (bv_unsigned ra :: outer) /\ uw_chain m sp s0 outer
  /\ cg_has (rt_cg RT Σ) PSTR_SITES PSTR_CALLS
  /\ (length (rt_frames RT Σ) < FRAMES_MAX)%nat /\ Z.of_nat (length (rt_live RT Σ)) + 3 <= LIVE_MAX /\ 1 <= rt_credit RT Σ
  /\ cl_env m lb canary
  (* [comment removed for export] *)
  /\ ro_bytes asegs S (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str /\ str <> [] /\ Z.of_nat (length str) + 16 <= 64512
  /\ (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
  /\ GOBJ b sz /\ b <= S /\ S + Z.of_nat (length str) + 1 <= b + sz
  /\ 0x10000 <= S /\ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= SEGTOP_A
  (* [comment removed for export] *)
  /\ rw_cells asegs m CTX_PSD [C8 (Z_to_bv 64 ps)]
  /\ In (ps, 48) (rt_live RT Σ) /\ ps mod 16 = 0 /\ rw_cells asegs m ps (psd_cells pk pl1 pl2 ni vi pq1 pq2)
  /\ 0 <= ni < 2 ^ 20 /\ 0 <= vi < 2 ^ 20
  /\ In (pk, 40) (rt_live RT Σ) /\ pk mod 16 = 0 /\ rw_cells asegs m pk (mutex_cells z64 z64)
  /\ plh_rep m (t_of nm pl1 pl2) B items bks /\ incl (plh_L (t_of nm pl1 pl2) B bks) (rt_live RT Σ) /\ items < 15
  /\ Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks [])
  (* [comment removed for export] *)
  /\ In (q_of nm pq1 pq2, 56) (rt_live RT Σ) /\ q_of nm pq1 pq2 mod 8 = 0.

(* [comment removed for export] *)
Definition pstr_post_mem (m' : mem) (canary : word) (nm : bool) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (pnn : Z) : Prop :=
  cl_env m' (Z_to_bv 8 1) canary
  /\ rw_cells asegs m' CTX_PSD [C8 (Z_to_bv 64 ps)]
  /\ rw_cells asegs m' ps (psd_bump nm pk pl1 pl2 ni vi pq1 pq2)
  /\ rw_cells asegs m' pk (mutex_cells z64 z64)
  /\ plh_rep m' (t_of nm pl1 pl2) B (items + 1) (pstr_bks bks str pnn).
Definition blk_ok (p n : Z) : Prop := 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

(* [comment removed for export] *)
Definition pstr_first_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (canary : word)
    (nm : bool) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (pad comp cmpt freet copyt : word) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (pn D pnn : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (junk' : list byte),
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (cnt_of nm ni vi + 1)) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (pstr_W (pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks)) m m'
           /\ pstr_post_mem m' canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pnn
           /\ rw_cells asegs m' (q_of nm pq1 pq2) (sk_cells (Z_to_bv 64 1) pad (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) comp cmpt freet copyt)
           /\ rw_cells asegs m' D [CB 32 junk']) c
       /\ rt_live RT Σ' = (pnn, 24) :: (D, 32) :: (pn, Z.of_nat (length str) + 16) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 1
       /\ blk_ok pn (Z.of_nat (length str) + 16) /\ blk_ok D 32 /\ blk_ok pnn 24 /\ rt_cg RT Σ' = rt_cg RT Σ.

Definition pstr_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
    (nm : bool) (S b sz : Z) (str slack : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (pad nalloc comp cmpt freet copyt : word),
  pstr_pre Σ PMc ra sp tp s0 a0 a1 a2 a3 m lo outer lb canary nm S b sz str slack ps pk pl1 pl2 ni vi pq1 pq2 B items bks ->
  rw_cells asegs m (q_of nm pq1 pq2) (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_property_string m)))
    (pstr_first_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pad comp cmpt freet copyt).

(* [comment removed for export] *)
Definition pstr_room_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (canary : word)
    (nm : bool) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (D num nalloc : Z) (pad cmpt freet copyt : word) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (pn pnn : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (junk' : list byte),
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (cnt_of nm ni vi + 1)) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (pstr_W ((D, 8 * nalloc) :: pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks)) m m'
           /\ pstr_post_mem m' canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pnn
           /\ rw_cells asegs m' (q_of nm pq1 pq2) (sk_cells (Z_to_bv 64 (num + 1)) pad (Z_to_bv 64 D) z64 (Z_to_bv 64 nalloc) z64 cmpt freet copyt)
           /\ rw_cells asegs m' D [CB (Z.to_nat (8 * nalloc)) junk']) c
       /\ rt_live RT Σ' = (pnn, 24) :: (pn, Z.of_nat (length str) + 16) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 1
       /\ blk_ok pn (Z.of_nat (length str) + 16) /\ blk_ok pnn 24 /\ rt_cg RT Σ' = rt_cg RT Σ.

Definition pstr_room_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
    (nm : bool) (S b sz : Z) (str slack : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode))
    (D num nalloc s01 : Z) (pad cmpt freet copyt : word) (junk : list byte),
  pstr_pre Σ PMc ra sp tp s0 a0 a1 a2 a3 m lo outer lb canary nm S b sz str slack ps pk pl1 pl2 ni vi pq1 pq2 B items bks ->
  rw_cells asegs m (q_of nm pq1 pq2) (sk_cells (Z_to_bv 64 num) pad (Z_to_bv 64 D) (Z_to_bv 64 s01) (Z_to_bv 64 nalloc) z64 cmpt freet copyt) ->
  (s01 = 0 \/ s01 = 1) -> 1 <= num -> num + 1 <= nalloc -> (nalloc = 4 \/ nalloc = 6) ->
  In (D, 8 * nalloc) (rt_live RT Σ) -> D mod 8 = 0 -> D <> ps -> rw_cells asegs m D [CB (Z.to_nat (8 * nalloc)) junk] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_property_string m)))
    (pstr_room_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks D num nalloc pad cmpt freet copyt).

(* [comment removed for export] *)
Definition pstr_grow_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (canary : word)
    (nm : bool) (str : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (D : Z) (pad cmpt freet copyt : word) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (pn D' pnn : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (junk' : list byte),
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (cnt_of nm ni vi + 1)) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) (pstr_W (pstr_L nm ps pk pl1 pl2 pq1 pq2 B bks)) m m'
           /\ pstr_post_mem m' canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks pnn
           /\ rw_cells asegs m' (q_of nm pq1 pq2) (sk_cells (Z_to_bv 64 5) pad (Z_to_bv 64 D') z64 (Z_to_bv 64 6) z64 cmpt freet copyt)
           /\ rw_cells asegs m' D' [CB 48 junk']) c
       /\ rt_live RT Σ' = (pnn, 24) :: (D', 48) :: (pn, Z.of_nat (length str) + 16) :: live_remove D (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 1
       /\ blk_ok pn (Z.of_nat (length str) + 16) /\ blk_ok D' 48 /\ blk_ok pnn 24 /\ rt_cg RT Σ' = rt_cg RT Σ.

Definition pstr_grow_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
    (nm : bool) (S b sz : Z) (str slack : list byte) (ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode))
    (D : Z) (pad cmpt freet copyt : word) (src : list byte),
  pstr_pre Σ PMc ra sp tp s0 a0 a1 a2 a3 m lo outer lb canary nm S b sz str slack ps pk pl1 pl2 ni vi pq1 pq2 B items bks ->
  rw_cells asegs m (q_of nm pq1 pq2) (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 D) z64 (Z_to_bv 64 4) z64 cmpt freet copyt) ->
  In (D, 32) (rt_live RT Σ) -> rw_cells asegs m D [CB 32 src] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_property_string m)))
    (pstr_grow_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m canary nm str ps pk pl1 pl2 ni vi pq1 pq2 B items bks D pad cmpt freet copyt).

End PstrStmts.
