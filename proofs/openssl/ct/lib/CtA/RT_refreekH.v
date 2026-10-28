(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeE RT_freeH RT_refreekA RT_refreekC RT_refreekD RT_refreekL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma aclient_split_r : forall (Σ : rtsA) (live0 : list (Z * Z)) usp x, geo_ok Σ -> l_ACEIL (lay Σ) + 0xFFB0 <= usp ->
  (forall p n, In (p, n) live0 ->
      (exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) /\ p = p_ubeg (l_SB (lay Σ)) c i n)
      \/ (exists k s, nth_error (sec Σ) k = Some s /\ s_quar s = false /\ s_n s = n /\ p = s_ubeg s)) ->
  aclient live0 (frames Σ) usp x -> outside [(l_ACEIL (lay Σ), usp)] x.
Proof.
  intros Σ live0 usp x HG Hsp HL Hx.
  pose proof (Z.le_refl (l_ACEIL (lay Σ))) as HR.
  apply (kv_client Σ [(l_ACEIL (lay Σ), usp)] [] [] [] usp HG (sk_img Σ _ usp HG HR) (sk_grant Σ _ usp HG HR)
           (sk_slot Σ _ usp HG HR) (sk_shad_app Σ _ usp HG HR) (sk_secmap Σ _ usp HG HR)
           ltac:(intros a n H1 H2; cbn [disjoint_from]; split; [lia | exact I]) ltac:(apply Forall_forall; intros; exact I) live0); [| exact Hx].
  - intros p n Hin. destruct (HL p n Hin) as [(c & i & Hc & Hn & ->)|(k & s & Hk & Hq & Hsn & ->)]; [left | right].
    + exists c, i. split; [exact Hc|]. split; [exact Hn|]. split; [reflexivity | intros []].
    + exists k, s. split; [exact Hk|]. split; [exact Hq|]. split; [exact Hsn|]. split; [reflexivity | intros []].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)