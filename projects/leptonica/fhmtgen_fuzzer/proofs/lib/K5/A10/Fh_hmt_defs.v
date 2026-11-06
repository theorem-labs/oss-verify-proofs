(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs D_libiface Lept_iface Gm_iface Fh_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition fh_hmt_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs name : Z) (vs : pixv) (cvs : cmapv) (i : nat) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> a2 = Z_to_bv 64 name ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_data vs <> 0 -> hm_name_arg RT Σ m name i ->
  uctx m sp s0 ras -> bv_unsigned ra = 0x9100c -> ras = [RA_TOP] ->
  LIB_SEL m -> lenv RT Σ m sp lo (LSTK 12) -> lres RT Σ 5 12 HMT_COST -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixHMTDwa_1 m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (v : pixv) (cv : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ new_pix1 RT Σ Σ' m' r (p_w vs) (p_h vs) v cv) c
       /\ new_pix1_live RT Σ Σ' r v cv
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - HMT_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition HMT_RA_ADDB : Z := 0xa91f8.      (* [comment removed for export] *)
Definition HMT_RA_GEN : Z := 0xa920c.       (* [comment removed for export] *)
Definition HMT_RA_RMB : Z := 0xa9218.       (* [comment removed for export] *)
Definition HMT_RA_D1 : Z := 0xa9224.        (* [comment removed for export] *)
Definition HMT_RA_D2 : Z := 0xa922c.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition HMT_RAS : list Z := [0x9100c; RA_TOP].

(* [comment removed for export] *)
Lemma hmt_tr_addb : In (RA_CMAPCOPY_CALLOC1 :: 0x9652c :: HMT_RA_ADDB :: HMT_RAS) CLIENT_TRACES.
Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma hmt_tr_rmb : In (RA_CMAPCOPY_CALLOC1 :: 0x96b00 :: HMT_RA_RMB :: HMT_RAS) CLIENT_TRACES.
Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma hmt_tr_d1 : Forall (fun f => In (f :: HMT_RA_D1 :: HMT_RAS) CLIENT_TRACES) DESTROY_FREE_RAS.
Proof. apply Forall_forall. intros f Hf. apply ct_mem_In. unfold DESTROY_FREE_RAS in Hf. cbn [In] in Hf.
  repeat (destruct Hf as [<-|Hf]; [vm_compute; reflexivity|]). destruct Hf. Qed.
Lemma hmt_tr_d2 : Forall (fun f => In (f :: HMT_RA_D2 :: HMT_RAS) CLIENT_TRACES) DESTROY_FREE_RAS.
Proof. apply Forall_forall. intros f Hf. apply ct_mem_In. unfold DESTROY_FREE_RAS in Hf. cbn [In] in Hf.
  repeat (destruct Hf as [<-|Hf]; [vm_compute; reflexivity|]). destruct Hf. Qed.
