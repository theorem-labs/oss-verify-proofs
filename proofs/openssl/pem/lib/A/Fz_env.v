(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex I_ut RT_iface_pem Fz_kit Fz_M_malloc Fz_M_zalloc Fz_M_locknew.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition e_CRYPTO_realloc : Z := 0x1fc320.
Definition e_CRYPTO_free : Z := 0x1fc430.
Definition CL_REALLOC_IMPL : Z := 0x5a9f60.   (* [comment removed for export] *)
Definition CL_FREE_IMPL : Z := 0x5a9f80.      (* [comment removed for export] *)
Definition CL_MEMSET_FUNC : Z := 0x5a9fc0.    (* [comment removed for export] *)
Definition e_wrap_memset : Z := 0x1c1918.

(* [comment removed for export] *)
Definition CL_RO : list (Z * list cell) :=
  [ (G_MALLOC_IMPL, [C8 (Z_to_bv 64 e_CRYPTO_malloc)]);
    (CL_REALLOC_IMPL, [C8 (Z_to_bv 64 e_CRYPTO_realloc)]);
    (CL_FREE_IMPL, [C8 (Z_to_bv 64 e_CRYPTO_free)]);
    (CL_MEMSET_FUNC, [C8 (Z_to_bv 64 e_wrap_memset)]) ].

Definition cl_env (m : mem) (lb : byte) (canary : word) : Prop :=
  Forall (fun p => ro_cells asegs m (fst p) (snd p)) CL_RO
  /\ rw_cells asegs m G_ALLOW_CUST [C1 lb] /\ (lb = Z_to_bv 8 0 \/ lb = Z_to_bv 8 1)
  /\ rw_cells asegs m ssp_guard [C8 canary].

(* [comment removed for export] *)
Definition CL_CELLS : list (Z * Z) :=
  [ (G_MALLOC_IMPL, G_MALLOC_IMPL + 8); (CL_REALLOC_IMPL, CL_REALLOC_IMPL + 8); (CL_FREE_IMPL, CL_FREE_IMPL + 8); (CL_MEMSET_FUNC, CL_MEMSET_FUNC + 8);
    (G_ALLOW_CUST, G_ALLOW_CUST + 1); (ssp_guard, ssp_guard + 8) ].
Definition cl_cell (x : Z) : Prop := in_ranges CL_CELLS x.

Lemma cl_cell_static : forall x, cl_cell x -> client_static x.
Proof.
  intros x (lo & hi & Hin & Hx). apply client_static_intro. unfold CL_CELLS, G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard in Hin.
  cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Lemma cl_cell_intro : forall lo hi x, In (lo, hi) CL_CELLS -> lo <= x < hi -> cl_cell x.
Proof. intros lo hi x Hin Hx. exists lo, hi. split; assumption. Qed.

(* [comment removed for export] *)
Lemma cl_env_mimp : forall m lb c, cl_env m lb c -> ro_cells asegs m G_MALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_malloc)].
Proof. intros m lb c (H & _). exact (proj1 (Forall_forall _ _) H (_, _) ltac:(left; reflexivity)). Qed.
Lemma cl_env_rimp : forall m lb c, cl_env m lb c -> ro_cells asegs m CL_REALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_realloc)].
Proof. intros m lb c (H & _). exact (proj1 (Forall_forall _ _) H (_, _) ltac:(right; left; reflexivity)). Qed.
Lemma cl_env_fimp : forall m lb c, cl_env m lb c -> ro_cells asegs m CL_FREE_IMPL [C8 (Z_to_bv 64 e_CRYPTO_free)].
Proof. intros m lb c (H & _). exact (proj1 (Forall_forall _ _) H (_, _) ltac:(right; right; left; reflexivity)). Qed.
Lemma cl_env_msf : forall m lb c, cl_env m lb c -> ro_cells asegs m CL_MEMSET_FUNC [C8 (Z_to_bv 64 e_wrap_memset)].
Proof. intros m lb c (H & _). exact (proj1 (Forall_forall _ _) H (_, _) ltac:(right; right; right; left; reflexivity)). Qed.
Lemma cl_env_lat : forall m lb c, cl_env m lb c -> rw_cells asegs m G_ALLOW_CUST [C1 lb].
Proof. intros m lb c (_ & H & _). exact H. Qed.
Lemma cl_env_hlb : forall m lb c, cl_env m lb c -> lb = Z_to_bv 8 0 \/ lb = Z_to_bv 8 1.
Proof. intros m lb c (_ & _ & H & _). exact H. Qed.
Lemma cl_env_guard : forall m lb c, cl_env m lb c -> rw_cells asegs m ssp_guard [C8 c].
Proof. intros m lb c (_ & _ & _ & H). exact H. Qed.

(* [comment removed for export] *)
Lemma wr_at_wseg8 : forall (m : mem) a,
  (forall i, In i [0;1;2;3;4;5;6;7] -> wview asegs (fun _ => None) (wa (a + i)) <> None) -> 0 <= a -> a + 8 <= 2^64 -> wr_at asegs m a 8.
Proof.
  intros m a H H0 H1. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  assert (Hin : In i [0;1;2;3;4;5;6;7]) by (cbn [In]; lia).
  specialize (H i Hin). unfold wview in *. destruct (m (wa (a + i))); [discriminate| exact H].
Qed.
Lemma got_ssp_wr : forall m : mem, wr_at asegs m got_ssp 8.
Proof.
  intros m. apply wr_at_wseg8; [| unfold got_ssp; lia | unfold got_ssp; lia].
  intros i Hi. cbn [In] in Hi. repeat (destruct Hi as [<-|Hi]; [vm_compute; discriminate|]). destruct Hi.
Qed.
Lemma got_ssp_ut : forall m : mem, img_untouched m -> rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
Proof.
  intros m U. split; [| exact (got_ssp_wr m)].
  apply (ut_ro_cells m got_ssp _ U); [exact (conj I I) | vm_compute; reflexivity | unfold IMG_UT_LO, got_ssp; lia | unfold IMG_UT_HI, got_ssp; cbn; lia].
Qed.
Lemma cl_env_ssp : forall m lb c, img_untouched m -> cl_env m lb c -> ssp_cells m c.
Proof. intros m lb c U E. split; [exact (got_ssp_ut m U) | exact (cl_env_guard m lb c E)]. Qed.
(* [comment removed for export] *)
Lemma got_cmalloc_ut : forall m : mem, img_untouched m -> ro_cells asegs m G_GOT_CMALLOC [C8 (Z_to_bv 64 e_CRYPTO_malloc)].
Proof.
  intros m U. apply (ut_ro_cells m G_GOT_CMALLOC _ U); [exact (conj I I) | vm_compute; reflexivity | unfold IMG_UT_LO, G_GOT_CMALLOC; lia | unfold IMG_UT_HI, G_GOT_CMALLOC; cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cl_env_agree : forall (m m' : mem) lb c, cl_env m lb c -> (forall a : word, cl_cell (bv_unsigned a) -> m' a = m a) -> cl_env m' lb c.
Proof.
  intros m m' lb c (RO & LAT & HLB & G) AG.
  split; [| split; [| split; [exact HLB|]]].
  - apply Forall_forall. intros (a, cs) Hin. pose proof (proj1 (Forall_forall _ _) RO (a, cs) Hin) as X. cbn [fst snd] in *.
    apply (ro_cells_agree asegs m m' _ _ X). intros x Hx. cbv beta in Hx. apply AG.
    unfold CL_RO in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; cbn [cells_size csize Nat.add] in Hx;
      first [ apply (cl_cell_intro G_MALLOC_IMPL (G_MALLOC_IMPL + 8)); [unfold CL_CELLS; cbn [In]; tauto | lia]
            | apply (cl_cell_intro CL_REALLOC_IMPL (CL_REALLOC_IMPL + 8)); [unfold CL_CELLS; cbn [In]; tauto | lia]
            | apply (cl_cell_intro CL_FREE_IMPL (CL_FREE_IMPL + 8)); [unfold CL_CELLS; cbn [In]; tauto | lia]
            | apply (cl_cell_intro CL_MEMSET_FUNC (CL_MEMSET_FUNC + 8)); [unfold CL_CELLS; cbn [In]; tauto | lia] ]|]).
    destruct Hin.
  - apply (rw_cells_agree_nw asegs m m' _ _ LAT). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AG.
    apply (cl_cell_intro G_ALLOW_CUST (G_ALLOW_CUST + 1)); [unfold CL_CELLS; cbn [In]; tauto | lia].
  - apply (rw_cells_agree_nw asegs m m' _ _ G). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AG.
    apply (cl_cell_intro ssp_guard (ssp_guard + 8)); [unfold CL_CELLS; cbn [In]; tauto | lia].
Qed.

(* [comment removed for export] *)
Definition cl_fp (W : list (Z * Z)) : Prop := forall x, cl_cell x -> outside W x.
Lemma cl_env_seg : forall W (m m' : mem) lb c, cl_env m lb c -> munch W m m' -> cl_fp W -> cl_env m' lb c.
Proof. intros W m m' lb c E MU HW. apply (cl_env_agree m m' lb c E). intros a Ha. exact (MU a (HW _ Ha)). Qed.

Lemma cl_fp_nil : cl_fp [].
Proof. intros x _. exact I. Qed.
Lemma cl_fp_cons : forall lo hi W,
  (hi <= G_MALLOC_IMPL \/ ssp_guard + 8 <= lo
   \/ (CL_MEMSET_FUNC + 8 <= lo /\ hi <= G_ALLOW_CUST) \/ (G_ALLOW_CUST + 1 <= lo /\ hi <= ssp_guard) \/ (CL_FREE_IMPL + 8 <= lo /\ hi <= CL_MEMSET_FUNC)
   \/ (G_MALLOC_IMPL + 8 <= lo /\ hi <= CL_REALLOC_IMPL) \/ (CL_REALLOC_IMPL + 8 <= lo /\ hi <= CL_FREE_IMPL)) ->
  cl_fp W -> cl_fp ((lo, hi) :: W).
Proof.
  intros lo hi W H HW x Hx. cbn [outside]. split; [| exact (HW x Hx)].
  destruct Hx as (l & h & Hin & Hx). unfold CL_CELLS, G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard in *. cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.
Lemma cl_fp_app : forall W1 W2, cl_fp W1 -> cl_fp W2 -> cl_fp (W1 ++ W2).
Proof. intros W1 W2 H1 H2 x Hx. apply outside_app_intro; [exact (H1 x Hx) | exact (H2 x Hx)]. Qed.
(* [comment removed for export] *)
Ltac cl_fp_lia :=
  repeat first [ apply cl_fp_nil | apply cl_fp_app
               | apply cl_fp_cons; [unfold G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard, USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in *; lia|] ].

(* [comment removed for export] *)
Lemma cl_env_pres : forall live frames sp (m m' : mem) lb c, cl_env m lb c -> rt_pres live frames sp m m' -> cl_env m' lb c.
Proof. intros live frames sp m m' lb c E P. apply (cl_env_agree m m' lb c E). intros a Ha. apply P. right; left. exact (cl_cell_static _ Ha). Qed.
Lemma cl_env_pres_ex : forall live frames sp d n (m m' : mem) lb c, cl_env m lb c -> rt_pres_ex live frames sp d n m m' ->
  (forall x, cl_cell x -> ~ (d <= x < d + n)) -> cl_env m' lb c.
Proof.
  intros live frames sp d n m m' lb c E P HD. apply (cl_env_agree m m' lb c E). intros a Ha.
  apply P; [right; left; exact (cl_cell_static _ Ha) | exact (HD _ Ha)].
Qed.
(* [comment removed for export] *)
Lemma cl_env_latch : forall live frames sp (m m' : mem) lb c, cl_env m lb c ->
  rt_pres_fp live frames sp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m' -> rw_cells asegs m' G_ALLOW_CUST [C1 (Z_to_bv 8 1)] ->
  cl_env m' (Z_to_bv 8 1) c.
Proof.
  intros live frames sp m m' lb c (RO & LAT & HLB & G) P LAT'.
  assert (AG : forall a : word, cl_cell (bv_unsigned a) -> ~ (G_ALLOW_CUST <= bv_unsigned a < G_ALLOW_CUST + 1) -> m' a = m a).
  { intros a Ha Hn. apply P; [right; left; exact (cl_cell_static _ Ha)|]. cbn [outside]. split; [exact Hn | exact I]. }
  split; [| split; [exact LAT' | split; [right; reflexivity|]]].
  - apply Forall_forall. intros (a, cs) Hin. pose proof (proj1 (Forall_forall _ _) RO (a, cs) Hin) as X. cbn [fst snd] in *.
    apply (ro_cells_agree asegs m m' _ _ X). intros x Hx. cbv beta in Hx.
    unfold CL_RO in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; cbn [cells_size csize Nat.add] in Hx; apply AG;
      [ first [ apply (cl_cell_intro G_MALLOC_IMPL (G_MALLOC_IMPL + 8)); [unfold CL_CELLS; cbn [In]; tauto | lia]
              | apply (cl_cell_intro CL_REALLOC_IMPL (CL_REALLOC_IMPL + 8)); [unfold CL_CELLS; cbn [In]; tauto | lia]
              | apply (cl_cell_intro CL_FREE_IMPL (CL_FREE_IMPL + 8)); [unfold CL_CELLS; cbn [In]; tauto | lia]
              | apply (cl_cell_intro CL_MEMSET_FUNC (CL_MEMSET_FUNC + 8)); [unfold CL_CELLS; cbn [In]; tauto | lia] ]
      | unfold G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST in *; lia ]|]).
    destruct Hin.
  - apply (rw_cells_agree_nw asegs m m' _ _ G). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AG.
    + apply (cl_cell_intro ssp_guard (ssp_guard + 8)); [unfold CL_CELLS; cbn [In]; tauto | lia].
    + unfold ssp_guard, G_ALLOW_CUST in *. lia.
Qed.

(* [comment removed for export] *)
Section EnvStmts.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Definition crypto_malloc_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (n lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba3ef0 -> 1 <= n <= 0x8000000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 48 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_malloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_cm_malloc, e_malloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_malloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ wr_at asegs m' p n /\ acc asegs m' p n) c
       /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Lemma crypto_malloc_env : crypto_malloc_stmt RT -> crypto_malloc_env_stmt.
Proof.
  intros H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo outer lb canary
    FDO MST E0 Etp Hn ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  eapply cps_conseq;
    [ exact (H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo outer lb
               FDO MST E0 Etp Hn ART0 MI0 CALL HSTK CTX UWC (proj1 CGH _ (or_introl eq_refl)) (proj2 CGH _ (or_introl eq_refl)) Hlen Hcr
               (cl_env_mimp m lb canary ENV) (got_cmalloc_ut m UT) (cl_env_lat m lb canary ENV) (cl_env_hlb m lb canary ENV))
    | intros c Hc; exact Hc |].
  intros c (Σ' & p & HA & REST). exists Σ', p. split; [| exact REST].
  apply (ASTA_conseq RT Σ' PMc _ _ c HA). intros ms (m' & RS & AFT & PRES & LAT' & WR & ACC). exists m'.
  split; [exact RS|]. split; [exact AFT|]. split; [exact PRES|].
  split; [exact (cl_env_latch _ _ _ m m' lb canary ENV PRES LAT')|]. split; assumption.
Qed.

Definition crypto_zalloc_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (n lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba3ef0 -> 1 <= n <= 0x4000000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_zalloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_zalloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ wr_at asegs m' p n /\ acc asegs m' p n
           /\ bytes_at asegs m' p (repeat (Z_to_bv 8 0) (Z.to_nat n))) c
       /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Lemma crypto_zalloc_env : crypto_zalloc_stmt RT -> crypto_zalloc_env_stmt.
Proof.
  intros H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo outer lb canary
    FDO MST E0 Etp Hn ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  eapply cps_conseq;
    [ exact (H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo outer lb
               FDO MST E0 Etp Hn ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr
               (cl_env_mimp m lb canary ENV) (got_cmalloc_ut m UT) (cl_env_lat m lb canary ENV) (cl_env_hlb m lb canary ENV))
    | intros c Hc; exact Hc |].
  intros c (Σ' & p & HA & REST). exists Σ', p. split; [| exact REST].
  apply (ASTA_conseq RT Σ' PMc _ _ c HA). intros ms (m' & RS & AFT & PRES & LAT' & WR & ACC & ZER). exists m'.
  split; [exact RS|]. split; [exact AFT|]. split; [exact PRES|].
  split; [exact (cl_env_latch _ _ _ m m' lb canary ENV PRES LAT')|]. split; [exact WR|]. split; assumption.
Qed.

Definition crypto_lock_new_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x200 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_lock_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                      [(SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 1 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_lock_new m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' p (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ acc asegs m' p 40) c
       /\ rt_live RT Σ' = (p, 40) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < p /\ p mod 16 = 0 /\ p + 40 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Lemma crypto_lock_new_env : crypto_lock_new_stmt RT -> crypto_lock_new_env_stmt.
Proof.
  intros H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST Etp ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  eapply cps_conseq;
    [ exact (H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
               FDO MST Etp ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr
               (cl_env_mimp m lb canary ENV) (got_cmalloc_ut m UT) (cl_env_lat m lb canary ENV) (cl_env_hlb m lb canary ENV) (cl_env_ssp m lb canary UT ENV))
    | intros c Hc; exact Hc |].
  intros c (Σ' & p & HA & REST). exists Σ', p. split; [| exact REST].
  apply (ASTA_conseq RT Σ' PMc _ _ c HA). intros ms (m' & RS & AFT & PRES & LAT' & SSP' & MX & ACC). exists m'.
  split; [exact RS|]. split; [exact AFT|]. split; [exact PRES|].
  split; [exact (cl_env_latch _ _ _ m m' lb canary ENV PRES LAT')|]. split; assumption.
Qed.

End EnvStmts.
