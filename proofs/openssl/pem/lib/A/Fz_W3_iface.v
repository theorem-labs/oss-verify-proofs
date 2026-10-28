(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_libiface_pem D_agree Fz_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_writec Fz_W1_read Fz_W1_pploc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TP_A : Z := 0xba3ef0.
Definition FZ_FUZZ_ONE : Z := 0x1f30b0.         (* [comment removed for export] *)
Definition FZ_PEM_READ_BIO : Z := 0x30c090.     (* [comment removed for export] *)
Definition FZ_SANITIZE : Z := 0x30cdf4.         (* [comment removed for export] *)
Definition FZ_PEM_MALLOC : Z := 0x30cd48.       (* [comment removed for export] *)
Definition FZ_PEM_FREE : Z := 0x30cd98.         (* [comment removed for export] *)
Definition FZ_BIO_NEW : Z := 0x236990.          (* [comment removed for export] *)
Definition FZ_BIO_FREE : Z := 0x2369b8.         (* [comment removed for export] *)
Definition FZ_BIO_READ : Z := 0x237054.         (* [comment removed for export] *)
Definition FZ_BIO_WRITE : Z := 0x2375b4.        (* [comment removed for export] *)
Definition FZ_BIO_PUTS : Z := 0x237be4.         (* [comment removed for export] *)
Definition FZ_BIO_GETS : Z := 0x238010.         (* [comment removed for export] *)
Definition FZ_BIO_CTRL : Z := 0x236dbc.         (* [comment removed for export] *)
Definition FZ_EVP_CTX_NEW : Z := 0x31eba8.      (* [comment removed for export] *)
Definition FZ_EVP_CTX_FREE : Z := 0x31ebdc.     (* [comment removed for export] *)
Definition FZ_ERR_NEW : Z := 0x1fc628.          (* [comment removed for export] *)
Definition FZ_ERR_SET_DEBUG : Z := 0x1fc940.
Definition FZ_ERR_SET_ERROR : Z := 0x1fcbb4.    (* [comment removed for export] *)
Definition FZ_ERR_CLEAR : Z := 0x1fd924.        (* [comment removed for export] *)
Definition M_MEM : Z := M_MEM_A.                (* [comment removed for export] *)
Definition M_SECMEM : Z := M_SECMEM_A.          (* [comment removed for export] *)
Definition PEM_FLAG_SECURE : Z := 1.
Definition PEM_FLAG_EAY_COMPATIBLE : Z := 2.
Definition PEM_FLAG_ONLY_B64 : Z := 4.
Definition LBUF : Z := 256.
Definition fsec (flags : Z) : Z := Z.land flags 1.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition apost (RT : rt_sig) (Σ Σ' : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (KEEP : list (Z * Z)) (W : list (Z * Z)) (canary : word)
    (R : word -> mem -> Prop) : config -> Prop :=
  ASTA RT Σ' PMc (fun ms => exists (v : word) (m' : mem),
       ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
    /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
    /\ rt_pres_fp KEEP (rt_frames RT Σ) (bv_unsigned sp) W m m'
    /\ cl_env m' (Z_to_bv 8 1) canary
    /\ R v m').

(* [comment removed for export] *)
Definition rts_same (RT : rt_sig) (Σ Σ' : rts RT) (k : Z) : Prop :=
  rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - k <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record mbk : Type := MBK { k_bi : Z; k_bb : Z; k_bm : Z; k_rp : Z; k_d : option Z }.
Definition mbk_data (K : mbk) (pd : option Z) : mbk := MBK (k_bi K) (k_bb K) (k_bm K) (k_rp K) pd.
Definition mbio_blocks (K : mbk) : list Z := [k_bi K; k_bb K; k_bm K; k_rp K] ++ match k_d K with Some d => [d] | None => [] end.
(* [comment removed for export] *)
Definition mbio_ent (K : mbk) (max : Z) : list (Z * Z) :=
  [(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ match k_d K with Some d => [(d, max)] | None => [] end.
(* [comment removed for export] *)
Definition mbio_W (K : mbk) (max : Z) : list (Z * Z) := map (fun e => (fst e, fst e + snd e)) (mbio_ent K max).
Definition mbio_T (K : mbk) (p : Z) : Prop := In p (mbio_blocks K).
Fixpoint live_remove_all (ps : list Z) (live : list (Z * Z)) : list (Z * Z) :=
  match ps with [] => live | p :: ps' => live_remove p (live_remove_all ps' live) end.

(* [comment removed for export] *)
Definition mb_inner (live : list (Z * Z)) (m : mem) (K : mbk) (len max off : Z) (flw blw : word) : Prop :=
  exists rmaxw : word,
     In (k_bb K, 16) live /\ (k_bb K) mod 16 = 0 /\ rw_cells asegs m (k_bb K) [C8 (wz (k_bm K)); C8 (wz (k_rp K))]
  /\ In (k_bm K, 32) live /\ (k_bm K) mod 16 = 0 /\ In (k_rp K, 32) live /\ (k_rp K) mod 16 = 0
  /\ 0 <= off <= len /\ len <= max /\ max < 2 ^ 31 - 1
  /\ match k_d K with
     | None => max = 0 /\ rw_cells asegs m (k_bm K) [C8 blw; C8 (wz 0); C8 (wz 0); C8 flw] /\ rw_cells asegs m (k_rp K) (readp_cells 0 0 0 rmaxw flw)
     | Some d => exists junk, In (d, max) live /\ 0 < max /\ rw_cells asegs m (k_bm K) [C8 blw; C8 (wz d); C8 (wz max); C8 flw]
                 /\ rw_cells asegs m (k_rp K) (readp_cells len d off rmaxw flw) /\ length junk = Z.to_nat max /\ rw_cells asegs m d [CB (Z.to_nat max) junk]
     end.
(* [comment removed for export] *)
Definition mbio_repx (live : list (Z * Z)) (m : mem) (K : mbk) (BI BM : Z) (blw : word) (meth len max off : Z) : Prop :=
  exists (fl : Z) (rrw numw padw nr nw : word),
     BI = k_bi K /\ BM = k_bm K /\ In (BI, 128) live /\ BI mod 16 = 0 /\ List.NoDup (mbio_blocks K) /\ (meth = M_MEM \/ meth = M_SECMEM)
  /\ rw_cells asegs m BI (bio_head meth)
  /\ rw_cells asegs m (BI + 40) (bio_w1_cells (wz 1) (wz 1) fl rrw numw padw (wz (k_bb K))) /\ fl_ok fl
  /\ rw_cells asegs m (BI + 72) (bio_tail nr nw)
  /\ mb_inner live m K len max off (wz (msec meth)) blw.
Definition mbio_rep (live : list (Z * Z)) (m : mem) (K : mbk) (BI meth len max off : Z) : Prop :=
  exists BM, mbio_repx live m K BI BM (wz len) meth len max off.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CallIface.
  Variable RT : rt_sig.
  (* [comment removed for export] *)
  Variable GOBJ : Z -> Z -> Prop.
  (* [comment removed for export] *)
  Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
  Variable libenv_fp : list (Z * Z) -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  (* [comment removed for export] *)
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
  Definition incl_live (LBL live : list (Z * Z)) : Prop := forall e, In e LBL -> In e live.
  (* [comment removed for export] *)
  Definition lib_W (LBL : list (Z * Z)) : list (Z * Z) := LIB_W ++ map (fun e => (fst e, fst e + snd e)) LBL.
  (* [comment removed for export] *)
  Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.                (* [comment removed for export] *)
  Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.         (* [comment removed for export] *)
  Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
  (* [comment removed for export] *)
  Variables FZ_SITES FZ_CALLS : list (Z * Z).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PMAL_STACK : Z := 16 + 128 + 64.        (* [comment removed for export] *)
  Definition PFREE_STACK : Z := 16 + 128 + 64.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition pem_malloc_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (E n flags : Z),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz n -> a1 = wz flags -> 0 < n < 2 ^ 27 -> 0 <= flags < 2 ^ 32 ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + PMAL_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary -> sec_off m ->
    cg_ctx (rt_cg RT Σ) FZ_PEM_MALLOC (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    In (bv_unsigned ra, e_CRYPTO_malloc) (cg_call (rt_cg RT Σ)) -> In (bv_unsigned ra, e_CRYPTO_secure_malloc) (cg_call (rt_cg RT Σ)) ->
    Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_PEM_MALLOC m)))
      (fun c => exists (Σ' : rts RT) (p : Z) (junk : list byte),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) (lib_W LBL) canary
           (fun v m' => v = wz p /\ wmono asegs m m' /\ libenv m' LBL E /\ sec_off m' /\ length junk = Z.to_nat n /\ rw_cells asegs m' p [CB (Z.to_nat n) junk]) c
         /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ rt_cg RT Σ' = rt_cg RT Σ /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP).

  (* [comment removed for export] *)
  Definition pem_malloc0_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (E flags : Z),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz 0 -> a1 = wz flags -> 0 <= flags < 2 ^ 32 ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + PMAL_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary -> sec_off m ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_PEM_MALLOC m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) (lib_W LBL) canary
           (fun v m' => v = wz 0 /\ wmono asegs m m' /\ libenv m' LBL E /\ sec_off m') c
         /\ rts_same RT Σ Σ' 0).

  (* [comment removed for export] *)
  Definition pem_free_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (E p n num flags : Z),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz p -> a1 = wz flags -> a2 = wz num -> 0 <= num <= n -> num < 2 ^ 40 -> 1 <= n -> 0 <= flags < 2 ^ 32 ->
    In (p, n) (rt_live RT Σ) -> ~ In (p, n) LBL ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + PFREE_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary -> sec_off m ->
    cg_ctx (rt_cg RT Σ) FZ_PEM_FREE (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    In (bv_unsigned ra, e_CRYPTO_free) (cg_call (rt_cg RT Σ)) -> In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
    In (bv_unsigned ra, e_CRYPTO_secure_clear_free) (cg_call (rt_cg RT Σ)) ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_PEM_FREE m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (live_remove p (rt_live RT Σ)) (lib_W LBL) canary (fun _ m' => libenv m' LBL E /\ sec_off m') c
         /\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

  (* [comment removed for export] *)
  Definition pem_free_null_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (E num flags : Z),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz 0 -> a1 = wz flags -> a2 = wz num -> 0 <= num < 2 ^ 64 -> 0 <= flags < 2 ^ 32 ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + PFREE_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary -> sec_off m ->
    cg_ctx (rt_cg RT Σ) FZ_PEM_FREE (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    In (bv_unsigned ra, e_CRYPTO_free) (cg_call (rt_cg RT Σ)) -> In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
    In (bv_unsigned ra, e_CRYPTO_secure_clear_free) (cg_call (rt_cg RT Σ)) ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_PEM_FREE m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) (lib_W LBL) canary
           (fun _ m' => wmono asegs m m' /\ libenv m' LBL E /\ sec_off m') c
         /\ rts_same RT Σ Σ' 0).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SAN_STACK : Z := 112 + 64.

  Definition sanitize_line_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (LB len flags fcall : Z) (bs : list byte),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz LB -> a1 = wz len -> a2 = wz flags -> a3 = wz fcall ->
    1 <= len <= 254 -> 0 <= flags < 2 ^ 32 -> 0 <= fcall < 2 ^ 32 ->
    In (LB, 256) (rt_live RT Σ) -> LB mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB [CB 256 bs] -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + SAN_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_SANITIZE m)))
      (apost RT Σ Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) [(LB, LB + 256)] canary
         (fun v m' => exists (len' : Z) (bs' : list byte), v = wz len' /\ 1 <= len' <= len + 1 /\ (nth_error bs (Z.to_nat (len - 1)) = Some (Z_to_bv 8 10) -> len' <= len) /\ wmono asegs m m'
              /\ length bs' = 256%nat /\ rw_cells asegs m' LB [CB 256 bs']
              /\ nth_error bs' (Z.to_nat (len' - 1)) = Some (Z_to_bv 8 10) /\ nth_error bs' (Z.to_nat len') = Some (Z_to_bv 8 0))).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ERRN_STACK : Z := 224 + 96.             (* [comment removed for export] *)
  Definition ERRD_STACK : Z := 400 + 96.             (* [comment removed for export] *)
  Definition ERRS_STACK : Z := 512 + 96.             (* [comment removed for export] *)
  Definition ERRC_STACK : Z := 288 + 96.             (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition err_new_rest_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (E : Z),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) -> In (E, 904) (rt_live RT Σ) -> errst_at_rest E [] m ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + ERRN_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cg_ctx (rt_cg RT Σ) FZ_ERR_NEW (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_ERR_NEW m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) ((E, E + 904) :: lib_W LBL) canary
           (fun _ m' => wmono asegs m m' /\ libenv m' LBL E /\ errst_live E 1 0 [] m') c
         /\ rts_same RT Σ Σ' 1).

  (* [comment removed for export] *)
  Definition pem_lit_ok (L n : Z) (str : list byte) : Prop :=
    exists (b sz : Z) (slack : list byte),
         ro_bytes asegs L (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str /\ str <> [] /\ n = Z.of_nat (length str) + 1 /\ 1 < n <= 64
      /\ (- (L + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
      /\ GOBJ b sz /\ b <= L /\ L + Z.of_nat (length str) + 1 <= b + sz /\ 0x10000 <= L /\ L + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= SEGTOP_A.
  Definition err_set_debug_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (E SF nf SN nn line : Z)
           (fstr nstr : list byte),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz SF -> a1 = wz line -> a2 = wz SN -> 0 <= line < 2 ^ 31 ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) -> In (E, 904) (rt_live RT Σ) -> errst_live E 1 0 [] m ->
    pem_lit_ok SF nf fstr -> pem_lit_ok SN nn nstr ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + ERRD_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cg_ctx (rt_cg RT Σ) FZ_ERR_SET_DEBUG (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 2 <= LIVE_MAX -> 2 <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_ERR_SET_DEBUG m)))
      (fun c => exists (Σ' : rts RT) (QF QN : Z),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) ((E, E + 904) :: lib_W LBL) canary
           (fun _ m' => wmono asegs m m' /\ libenv m' LBL E /\ errst_live E 1 0 [(QN, nn); (QF, nf)] m') c
         /\ rt_live RT Σ' = (QN, nn) :: (QF, nf) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ - 2 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ /\ 0 < QF /\ 0 < QN).

  (* [comment removed for export] *)
  Definition err_set_error_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (E lib reason : Z) (strs : list (Z * Z)),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz lib -> a1 = wz reason -> a2 = wz 0 -> 0 < lib < 256 -> lib <> 2 -> 0 < reason < 2 ^ 31 ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) -> In (E, 904) (rt_live RT Σ) -> incl_live strs (rt_live RT Σ) -> errst_live E 1 0 strs m ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + ERRS_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cg_ctx (rt_cg RT Σ) FZ_ERR_SET_ERROR (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> 2 <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_ERR_SET_ERROR m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) ((E, E + 904) :: lib_W LBL) canary
           (fun _ m' => wmono asegs m m' /\ libenv m' LBL E /\ errst_live E 1 0 strs m') c
         /\ rts_same RT Σ Σ' 2).

  (* [comment removed for export] *)
  Definition err_clear_steady_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (E top bot : Z) (strs : list (Z * Z)),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) -> In (E, 904) (rt_live RT Σ) -> incl_live strs (rt_live RT Σ) ->
    (forall e, In e strs -> ~ In e LBL /\ e <> (E, 904)) -> List.NoDup (map fst strs) -> errst_live E top bot strs m ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + ERRC_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cg_ctx (rt_cg RT Σ) FZ_ERR_CLEAR (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_ERR_CLEAR m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (live_remove_all (map fst strs) (rt_live RT Σ)) ((E, E + 904) :: lib_W LBL) canary
           (fun _ m' => libenv m' LBL E /\ errst_at_rest E [] m') c
         /\ rt_live RT Σ' = live_remove_all (map fst strs) (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ - 1 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition BNEW_STACK : Z := 64 + 224 + 336 + 128.  (* [comment removed for export] *)
  Definition BFREE_STACK : Z := 32 + 32 + 224 + 400 + 128.   (* [comment removed for export] *)
  Definition BGETS_STACK : Z := 160 + 32 + 160 + 96.        (* [comment removed for export] *)
  Definition BPUTS_STACK : Z := 128 + 32 + 0x100 + 224 + 128. (* [comment removed for export] *)
  Definition BWRITE_STACK : Z := 32 + 160 + 32 + 32 + 0x100 + 224 + 128.
  Definition BREAD_STACK : Z := 96 + 32 + 96 + 32 + 160 + 96.
  Definition BCTRL_STACK : Z := 240 + 80.                    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition bio_new_res (meth : Z) (live : list (Z * Z)) : word -> list (Z * Z) -> mem -> Prop :=
    fun v live' m' => exists (K : mbk) (BI BB BM RP : Z),
         v = wz BI /\ K = MBK BI BB BM RP None
      /\ live' = (RP, 32) :: (BM, 32) :: (BB, 16) :: (BI, 128) :: live
      /\ mbio_rep live' m' K BI meth 0 0 0.
  Definition bio_new_mem_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (E meth : Z),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz meth -> (meth = M_MEM \/ meth = M_SECMEM) ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + BNEW_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cg_ctx (rt_cg RT Σ) FZ_BIO_NEW (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 4 <= LIVE_MAX -> 1 <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_NEW m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) (lib_W LBL) canary
           (fun v m' => wmono asegs m m' /\ libenv m' LBL E /\ bio_new_res meth (rt_live RT Σ) v (rt_live RT Σ') m') c
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ).

  (* [comment removed for export] *)
  Definition bio_free_mem_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (K : mbk) (E BI BM meth len max off : Z) (blw : word),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz BI ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) -> (forall e, In e LBL -> ~ In (fst e) (mbio_blocks K)) ->
    mbio_repx (rt_live RT Σ) m K BI BM blw meth len max off ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + BFREE_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary -> sec_off m ->
    cg_ctx (rt_cg RT Σ) FZ_BIO_FREE (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_FREE m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (live_remove_all (mbio_blocks K) (rt_live RT Σ)) (lib_W LBL) canary
           (fun v m' => v = wz 1 /\ libenv m' LBL E /\ sec_off m') c
         /\ rt_live RT Σ' = live_remove_all (mbio_blocks K) (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ - 1 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ).
  (* [comment removed for export] *)
  Definition bio_free_null_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz 0 ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 32 <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_FREE m)))
      (apost RT Σ Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) [] canary (fun v m' => v = wz 0 /\ wmono asegs m m')).

  (* [comment removed for export] *)
  Definition bio_gets_res (K : mbk) (BI meth len max off LB : Z) (bs : list byte) (live : list (Z * Z)) : word -> mem -> Prop :=
    fun v m' => exists (k : Z) (bs' : list byte), v = wz k /\ length bs' = 256%nat /\ rw_cells asegs m' LB [CB 256 bs']
      /\ ((k = 0 /\ off = len /\ mbio_rep live m' K BI meth len max off)
          \/ (1 <= k <= Z.min (len - off) 254 /\ nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 0) /\ (k < Z.min (len - off) 254 -> nth_error bs' (Z.to_nat (k - 1)) = Some (Z_to_bv 8 10)) /\ mbio_rep live m' K BI meth len max (off + k))).
  Definition bio_gets_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (K : mbk) (BI meth len max off LB : Z) (bs : list byte),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz BI -> a1 = wz LB -> a2 = wz 255 ->
    mbio_rep (rt_live RT Σ) m K BI meth len max off ->
    In (LB, 256) (rt_live RT Σ) -> LB mod 16 = 0 -> ~ mbio_T K LB -> length bs = 256%nat -> rw_cells asegs m LB [CB 256 bs] ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + BGETS_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_GETS m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) ((LB, LB + 256) :: mbio_W K max) canary
           (fun v m' => wmono asegs m m' /\ bio_gets_res K BI meth len max off LB bs (rt_live RT Σ) v m') c
         /\ rts_same RT Σ Σ' 1).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition puts_cost (len n max : Z) : Z := 1 + (if max <? len + n then mcost (gr_n (len + n)) else 0).
  (* [comment removed for export] *)
  Definition puts_lists (K : mbk) (pd' : option Z) (max max' : Z) (live live' : list (Z * Z)) : Prop :=
       (pd' = k_d K /\ max' = max /\ live' = live)
    \/ (exists q : Z, pd' = Some q /\ k_d K = None /\ live' = (q, max') :: live)
    \/ (exists q d : Z, pd' = Some q /\ k_d K = Some d /\ live' = (q, max') :: live_remove d live).
  Definition bio_puts_res (K : mbk) (BI meth len max n : Z) (live : list (Z * Z)) : word -> list (Z * Z) -> mem -> Prop :=
    fun v live' m' => exists (pd' : option Z) (max' : Z), v = wz n /\ (max' = max \/ (max < len + n /\ max' = gr_n (len + n))) /\ len + n <= max'
      /\ mbio_rep live' m' (mbk_data K pd') BI meth (len + n) max' 0
      /\ puts_lists K pd' max max' live live'.
  Definition bio_puts_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (K : mbk) (BI meth len max LB n : Z) (bs : list byte),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz BI -> a1 = wz LB ->
    mbio_rep (rt_live RT Σ) m K BI meth len max 0 -> gr_n (len + n) <= 2 ^ 27 ->
    In (LB, 256) (rt_live RT Σ) -> LB mod 16 = 0 -> ~ mbio_T K LB -> length bs = 256%nat -> rw_cells asegs m LB [CB 256 bs] ->
    0 <= n <= 255 -> nth_error bs (Z.to_nat n) = Some (Z_to_bv 8 0) -> (forall i, (i < Z.to_nat n)%nat -> nth_error bs i <> Some (Z_to_bv 8 0)) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + BPUTS_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary -> sec_off m ->
    cg_ctx (rt_cg RT Σ) FZ_BIO_PUTS (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> puts_cost len n max <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_PUTS m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m
               (match k_d K with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end)
               ((G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W K max) canary
           (fun v m' => sec_off m' /\ bio_puts_res K BI meth len max n (rt_live RT Σ) v (rt_live RT Σ') m') c
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - puts_cost len n max <= rt_credit RT Σ'
         /\ rt_cg RT Σ' = rt_cg RT Σ).

  (* [comment removed for export] *)
  Definition bio_write0_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (n : Z),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a2 = wz n -> - 2 ^ 31 <= n <= 0 ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 32 <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_WRITE m)))
      (apost RT Σ Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) [] canary (fun v m' => v = wz 0 /\ wmono asegs m m')).
  Definition bio_write_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (K : mbk) (BI meth len max IN n : Z) (src : list byte),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz BI -> a1 = wz IN -> a2 = wz n ->
    mbio_rep (rt_live RT Σ) m K BI meth len max 0 -> gr_n (len + n) <= 2 ^ 27 -> 0 < n < 2 ^ 31 ->
    bytes_at asegs m IN src -> length src = Z.to_nat n -> src_blk (rt_live RT Σ) IN n (mbio_blocks K) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + BWRITE_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary -> sec_off m ->
    cg_ctx (rt_cg RT Σ) FZ_BIO_WRITE (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> puts_cost len n max <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_WRITE m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m
               (match k_d K with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end)
               ((G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W K max) canary
           (fun v m' => sec_off m' /\ bio_puts_res K BI meth len max n (rt_live RT Σ) v (rt_live RT Σ') m') c
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - puts_cost len n max <= rt_credit RT Σ'
         /\ rt_cg RT Σ' = rt_cg RT Σ).
  (* [comment removed for export] *)
  Definition bio_writeg_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (K : mbk) (BI meth len max off IN n : Z) (src : list byte),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz BI -> a1 = wz IN -> a2 = wz n ->
    mbio_rep (rt_live RT Σ) m K BI meth len max off -> gr_n (len - off + n) <= 2 ^ 27 -> 0 < n < 2 ^ 31 ->
    bytes_at asegs m IN src -> length src = Z.to_nat n -> src_blk (rt_live RT Σ) IN n (mbio_blocks K) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + BWRITE_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary -> sec_off m ->
    cg_ctx (rt_cg RT Σ) FZ_BIO_WRITE (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> puts_cost (len - off) n max <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_WRITE m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m
               (match k_d K with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end)
               ((G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W K max) canary
           (fun v m' => sec_off m' /\ bio_puts_res K BI meth (len - off) max n (rt_live RT Σ) v (rt_live RT Σ') m') c
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - puts_cost (len - off) n max <= rt_credit RT Σ'
         /\ rt_cg RT Σ' = rt_cg RT Σ).

  (* [comment removed for export] *)
  Definition bio_ctrl_ptr_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (K : mbk) (BI meth len max off PP : Z) (old : word),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz BI -> a1 = wz 115 -> a2 = wz 0 -> a3 = wz PP ->
    mbio_rep (rt_live RT Σ) m K BI meth len max off ->
    PP mod 8 = 0 -> rw_cells asegs m PP [C8 old] -> pp_loc (rt_frames RT Σ) m (bv_unsigned sp) PP -> (forall e, In e (mbio_ent K max) -> PP + 8 <= fst e \/ fst e + snd e <= PP) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + BCTRL_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_CTRL m)))
      (apost RT Σ Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) ((PP, PP + 8) :: mbio_W K max) canary
         (fun v m' => exists BM, v = wz 1 /\ wmono asegs m m' /\ rw_cells asegs m' PP [C8 (wz BM)]
              /\ mbio_repx (rt_live RT Σ) m' K BI BM (wz (len - off)) meth (len - off) max 0)).

  (* [comment removed for export] *)
  Definition bio_ctrl_info_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (K : mbk) (BI meth len max off : Z),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz BI -> a1 = wz 3 -> a2 = wz 0 -> a3 = wz 0 ->
    mbio_rep (rt_live RT Σ) m K BI meth len max off ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + BCTRL_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_CTRL m)))
      (apost RT Σ Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) [] canary
         (fun v m' => v = wz (len - off) /\ wmono asegs m m' /\ mbio_rep (rt_live RT Σ) m' K BI meth len max off)).

  (* [comment removed for export] *)
  Definition bio_read_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (K : mbk) (BI BM meth len max off OUT no n : Z) (blw : word) (ojunk : list byte),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz BI -> a1 = wz OUT -> a2 = wz n ->
    mbio_repx (rt_live RT Σ) m K BI BM blw meth len max off -> 1 <= n <= len - off ->
    In (OUT, no) (rt_live RT Σ) -> ~ mbio_T K OUT -> n <= no -> length ojunk = Z.to_nat no -> rw_cells asegs m OUT [CB (Z.to_nat no) ojunk] ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + BREAD_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_BIO_READ m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) ((OUT, OUT + n) :: mbio_W K max) canary
           (fun v m' => exists ojunk' : list byte, v = wz n /\ wmono asegs m m' /\ mbio_repx (rt_live RT Σ) m' K BI BM blw meth len max (off + n)
                /\ length ojunk' = Z.to_nat no /\ rw_cells asegs m' OUT [CB (Z.to_nat no) ojunk']) c
         /\ rts_same RT Σ Σ' 1).

  (* [comment removed for export] *)
  Definition ECTX : Z := 92.
  Definition evp_ctx_new_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cg_ctx (rt_cg RT Σ) FZ_EVP_CTX_NEW (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    In (bv_unsigned ra, e_CRYPTO_zalloc) (cg_call (rt_cg RT Σ)) ->
    Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_EVP_CTX_NEW m)))
      (fun c => exists (Σ' : rts RT) (p : Z),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] canary
           (fun v m' => v = wz p /\ wmono asegs m m' /\ rw_cells asegs m' p [CB (Z.to_nat ECTX) (repeat (Z_to_bv 8 0) (Z.to_nat ECTX))]) c
         /\ rt_live RT Σ' = (p, ECTX) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ /\ 0 < p /\ p mod 16 = 0 /\ p + ECTX < USTACK_TOP).
  Definition evp_ctx_free_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (p : Z),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz p -> In (p, ECTX) (rt_live RT Σ) ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 16 + 16 <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cg_ctx (rt_cg RT Σ) FZ_EVP_CTX_FREE (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    In (bv_unsigned ra, e_CRYPTO_free) (cg_call (rt_cg RT Σ)) -> In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_EVP_CTX_FREE m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (live_remove p (rt_live RT Σ)) [] canary (fun _ _ => True) c
         /\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).
  Definition evp_ctx_free_null_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A -> a0 = wz 0 ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 16 + 16 <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary ->
    cg_ctx (rt_cg RT Σ) FZ_EVP_CTX_FREE (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    In (bv_unsigned ra, e_CRYPTO_free) (cg_call (rt_cg RT Σ)) -> In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_EVP_CTX_FREE m)))
      (apost RT Σ Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ) [] canary (fun _ m' => wmono asegs m m')).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PEM_CALLEE_STACK : Z := 1024.            (* [comment removed for export] *)
  Definition PEMR_STACK : Z := 352 + 32 + PEM_CALLEE_STACK.
  Definition pem_credit (plen : Z) : Z := 2 ^ 22 + 48 * plen.

  (* [comment removed for export] *)
  Definition pem_out (ret : Z) (m : mem) (PN PH PD PL : Z) (news : list (Z * Z)) : Prop :=
    (ret = 0 /\ news = [] /\ rw_cells asegs m PN [C8 (wz 0)] /\ rw_cells asegs m PH [C8 (wz 0)] /\ rw_cells asegs m PD [C8 (wz 0)] /\ (exists lw, rw_cells asegs m PL [C8 lw]))
    \/ (ret = 1 /\ exists (NM HD DT nn nh dlen : Z) (bn bh bd : list byte),
           news = [(DT, dlen); (HD, nh); (NM, nn)] /\ 1 <= nn <= 255 /\ 1 <= nh < 2 ^ 31 /\ 1 <= dlen < 2 ^ 31
        /\ rw_cells asegs m PN [C8 (wz NM)] /\ rw_cells asegs m PH [C8 (wz HD)] /\ rw_cells asegs m PD [C8 (wz DT)] /\ rw_cells asegs m PL [C8 (wz dlen)]
        /\ length bn = Z.to_nat nn /\ rw_cells asegs m NM [CB (Z.to_nat nn) bn] /\ In (Z_to_bv 8 0) bn
        /\ length bh = Z.to_nat nh /\ rw_cells asegs m HD [CB (Z.to_nat nh) bh] /\ nth_error bh (Z.to_nat (nh - 1)) = Some (Z_to_bv 8 0)
        /\ length bd = Z.to_nat dlen /\ rw_cells asegs m DT [CB (Z.to_nat dlen) bd]).
  Definition news_sz (news : list (Z * Z)) : Z := fold_right (fun e acc => snd e + acc) 0 news.

  (* [comment removed for export] *)
  Definition pem_read_res (K : mbk) (BI meth blen bmax boff PN PH PD PL E : Z) (LBL live : list (Z * Z)) : word -> list (Z * Z) -> mem -> Prop :=
    fun v live' m' => exists (ret boff' top bot : Z) (strs news : list (Z * Z)),
         v = wz ret /\ boff <= boff' <= blen /\ mbio_rep live' m' K BI meth blen bmax boff'
      /\ libenv m' LBL E /\ errst_live E top bot strs m' /\ (length strs <= 2)%nat /\ Forall (fun e => 0 < snd e <= 64) strs
      /\ List.NoDup (map fst (strs ++ news)) /\ 254 * news_sz news <= 255 * (boff' - boff) + 254 * 512
      /\ pem_out ret m' PN PH PD PL news
      /\ Permutation live' (strs ++ news ++ live) /\ (forall e, In e (strs ++ news) -> ~ In (fst e) (map fst live)).

  Definition pem_read_bio_stmt : Prop :=
    forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (canary : word) (LBL : list (Z * Z)) (K : mbk)
           (E BI meth blen bmax boff PN PH PD PL flags : Z) (on oh od ol : word),
    fdfs_only PMc -> mat_stable PMc -> tp = wz TP_A ->
    a0 = wz BI -> a1 = wz PN -> a2 = wz PH -> a3 = wz PD -> a4 = wz PL -> a5 = wz flags -> 0 <= flags < 256 ->
    libenv m LBL E -> incl_live LBL (rt_live RT Σ) -> In (E, 904) (rt_live RT Σ) -> ~ In (E, 904) LBL ->
    (forall e, In e ((E, 904) :: LBL) -> ~ In (fst e) (mbio_blocks K)) -> errst_at_rest E [] m ->
    mbio_rep (rt_live RT Σ) m K BI meth blen bmax boff -> blen < 2 ^ 26 ->
    (* [comment removed for export] *)
    List.NoDup [PN; PH; PD; PL] -> Forall (fun P => P mod 8 = 0 /\ pp_loc (rt_frames RT Σ) m USTACK_TOP P) [PN; PH; PD; PL] ->
    rw_cells asegs m PN [C8 on] -> rw_cells asegs m PH [C8 oh] -> rw_cells asegs m PD [C8 od] -> rw_cells asegs m PL [C8 ol] ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + PEMR_STACK <= bv_unsigned sp -> cl_env m (Z_to_bv 8 1) canary -> sec_off m ->
    cg_ctx (rt_cg RT Σ) FZ_PEM_READ_BIO (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FZ_SITES FZ_CALLS ->
    (length (rt_frames RT Σ) + 3 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 21 <= LIVE_MAX -> pem_credit (blen - boff) <= rt_credit RT Σ ->
    (forall e, In e (rt_live RT Σ) -> 0 < snd e) ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc FZ_PEM_READ_BIO m)))
      (fun c => exists (Σ' : rts RT),
         apost RT Σ Σ' PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m (rt_live RT Σ)
               ([(PN, PN + 8); (PH, PH + 8); (PD, PD + 8); (PL, PL + 8); (E, E + 904)] ++ mbio_W K bmax ++ lib_W LBL) canary
           (fun v m' => sec_off m' /\ pem_read_res K BI meth blen bmax boff PN PH PD PL E LBL (rt_live RT Σ) v (rt_live RT Σ') m') c
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - pem_credit (blen - boff) <= rt_credit RT Σ'
         /\ rt_cg RT Σ' = rt_cg RT Σ).

  (* [comment removed for export] *)
  Definition pem_read_bio_deps : Prop :=
    pem_malloc_stmt -> pem_malloc0_stmt -> pem_free_stmt -> pem_free_null_stmt -> sanitize_line_stmt ->
    err_new_rest_stmt -> err_set_debug_stmt -> err_set_error_stmt ->
    bio_new_mem_stmt -> bio_free_mem_stmt -> bio_gets_stmt -> bio_puts_stmt -> bio_ctrl_ptr_stmt -> bio_ctrl_info_stmt -> bio_read_stmt ->
    evp_ctx_new_stmt -> evp_ctx_free_stmt -> evp_ctx_free_null_stmt ->
    pem_read_bio_stmt.
  (* [comment removed for export] *)
End CallIface.
