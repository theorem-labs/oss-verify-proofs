(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs Lept_iface Gm_iface Fh_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition rmborder1_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 32 -> a2 = Z_to_bv 64 32 -> a3 = Z_to_bv 64 32 -> a4 = Z_to_bv 64 32 ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 1 -> p_data vs <> 0 -> 64 < p_w vs -> 64 < p_h vs ->
  (p_cmap vs <> 0 -> uctx m sp s0 ras /\ In (RA_CMAPCOPY_CALLOC1 :: 0x974f0 :: bv_unsigned ra :: ras) CLIENT_TRACES) ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 4 4 BORDER1_COST -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRemoveBorderGeneral m)))
    (fun c => exists (Σ' : rts RT) (r : Z) (v : pixv) (cv : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ new_pix1 RT Σ Σ' m' r (p_w vs - 64) (p_h vs - 64) v cv) c
       /\ new_pix1_live RT Σ Σ' r v cv
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - BORDER1_COST <= rt_credit RT Σ').

Lemma rmborder1_of_cases : forall RT, rmborder1_case RT 0 -> rmborder1_case RT 16 -> pixRemoveBorder1_cps RT e_pixRemoveBorderGeneral.
Proof.
  intros RT C0 C16 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pixs vs cvs ras H1 H2 H3 H4 ARGS H6 H7 H8 H9 H10 H11 ENV H13.
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16).
  { destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & SPA & _). Z.div_mod_to_equations. lia. }
  destruct ARGS as [(_ & E1 & E2 & E3 & E4)|(E & _)].
  2:{ exfalso. unfold e_pixRemoveBorderGeneral, e_pixRemoveBorder in E. lia. }
  destruct AL as [AL|AL]; [eapply C0| eapply C16]; eassumption.
Qed.
