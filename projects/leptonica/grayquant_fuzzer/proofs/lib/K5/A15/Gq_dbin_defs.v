(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env Gq_obj Gq_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DbinDefs.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition dbin_post (Σ : rts RT) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo pix : Z) (v : pixv) (cv : cmapv)
    : config -> Prop :=
  fun c => exists (Σ' : rts RT) (r : Z) (vr : pixv) (cvr : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pix + 20, pix + 24)] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v cv
          /\ (r = 0 \/ (pix_obj (rt_live RT Σ') m' r vr cvr /\ p_data vr <> 0))) c
       /\ (r = 0 -> rt_live RT Σ' = rt_live RT Σ)
       /\ (r <> 0 -> live_destroy r vr cvr (rt_live RT Σ') = rt_live RT Σ)
       /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n)
       /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - DBIN_COST 8 <= rt_credit RT Σ'.

(* [comment removed for export] *)
Definition dbin_spec_case (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 10 -> a2 = Z_to_bv 64 10 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 -> cmap_nz v cv -> p_d v = 8 ->
  uctx m sp s0 ras -> bv_unsigned ra = RA_FUZZ_OP2 -> ras = [RA_TOP] ->
  lenv RT Σ m sp lo (LSTK 11) -> lres RT Σ 6 12 (DBIN_COST 8) -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDitherToBinarySpec m)))
    (dbin_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo pix v cv).

End DbinDefs.

(* [comment removed for export] *)
Lemma live_remove_cons' : forall p e (l : list (Z * Z)), live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof. intros p e l. unfold live_remove. cbn. destruct (fst e =? p); cbn; reflexivity. Qed.
Lemma live_remove_notin : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l H. induction l as [|e l IH]; [reflexivity|].
  rewrite live_remove_cons'. destruct (Z.eqb_spec (fst e) p) as [E|NE]; [exfalso; exact (H e (or_introl eq_refl) E)|].
  f_equal. apply IH. intros e' He'. apply H. right. exact He'.
Qed.
Lemma live_remove_hd : forall p n (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p ((p, n) :: l) = l.
Proof.
  intros p n l H. rewrite live_remove_cons'. cbn [fst]. rewrite Z.eqb_refl. exact (live_remove_notin p l H).
Qed.
Lemma live_remove_2nd : forall p n q k (l : list (Z * Z)), q <> p -> (forall e, In e l -> fst e <> p) -> live_remove p ((q, k) :: (p, n) :: l) = (q, k) :: l.
Proof.
  intros p n q k l NE H. rewrite live_remove_cons'. cbn [fst]. destruct (Z.eqb_spec q p) as [E|_]; [exfalso; exact (NE E)|].
  f_equal. exact (live_remove_hd p n l H).
Qed.
