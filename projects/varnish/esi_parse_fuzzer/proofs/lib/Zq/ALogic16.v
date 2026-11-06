(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Obligations16.
Context {Clg : Ceiling}.
Context {DR : DepotRep}.

Definition pa_malloc_obligation16 : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n : Z) (T : TSet),
      let v := aview_of (pa_hull A) m in
      pa_ainv A m md -> mem_inv (cl_segs LPA) v ->
      a0 = wz n -> 1 <= n < REQ_MAX -> n <= NREQ_CAP ->
      as_livebytes A + n <= LIVE_MAX -> as_nlive A + 1 <= NLIVE_MAX -> (n < 16 -> 1 <= as_tinycred A) ->
      (kMaxPrimaryUser < n -> 1 <= as_seccred A) -> prim_cost n <= as_primcred A (* [comment removed for export] *) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites LPA) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A') m' in
          pa_ainv A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          hull_le (pa_hull A) (pa_hull A') ->
          (forall ff, as_fframe A' ff = as_fframe A ff) ->
          as_tinycred A' = as_tinycred A - (if Z.ltb n 16 then 1 else 0) ->
          (r <> 0 /\ as_live A r = None /\ as_live A' r = Some n /\
               (forall q, q <> r -> as_live A' q = as_live A q) /\
               as_livebytes A' = as_livebytes A + n /\ as_nlive A' = as_nlive A + 1 /\
               as_seccred A' = as_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) /\
               as_primcred A' = as_primcred A - prim_cost n (* [comment removed for export] *)) ->
          frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK nowhere (newblk r n)
                   (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' (seg_rom (cl_segs LPA))) md') T) ->
      srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_malloc_pc LPA) fc None m (seg_rom (cl_segs LPA))) md) T.

Definition pa_calloc_obligation16 : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (cnt sz : Z) (T : TSet),
      let v := aview_of (pa_hull A) m in
      pa_ainv A m md -> mem_inv (cl_segs LPA) v ->
      a0 = wz cnt -> a1 = wz sz -> 0 <= cnt < REQ_MAX -> 0 <= sz < REQ_MAX -> 1 <= cnt * sz < REQ_MAX -> cnt * sz <= NREQ_CAP ->
      as_livebytes A + cnt * sz <= LIVE_MAX -> as_nlive A + 1 <= NLIVE_MAX -> (cnt * sz < 16 -> 1 <= as_tinycred A) ->
      (kMaxPrimaryUser < cnt * sz -> 1 <= as_seccred A) -> prim_cost (cnt * sz) <= as_primcred A (* [comment removed for export] *) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites LPA) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A') m' in
          pa_ainv A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          hull_le (pa_hull A) (pa_hull A') ->
          (forall ff, as_fframe A' ff = as_fframe A ff) ->
          as_tinycred A' = as_tinycred A - (if Z.ltb (cnt * sz) 16 then 1 else 0) ->
          (r <> 0 /\ as_live A r = None /\ as_live A' r = Some (cnt * sz) /\
               (forall q, q <> r -> as_live A' q = as_live A q) /\ all_zero v' r (cnt * sz) /\
               as_livebytes A' = as_livebytes A + cnt * sz /\ as_nlive A' = as_nlive A + 1 /\
               as_seccred A' = as_seccred A - (if Z.ltb kMaxPrimaryUser (cnt * sz) then 1 else 0) /\
               as_primcred A' = as_primcred A - prim_cost (cnt * sz) (* [comment removed for export] *)) ->
          frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK nowhere (newblk r (cnt * sz))
                   (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' (seg_rom (cl_segs LPA))) md') T) ->
      srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_calloc_pc LPA) fc None m (seg_rom (cl_segs LPA))) md) T.

Definition pa_realloc_obligation16 : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n old : Z) (T : TSet),
      let v := aview_of (pa_hull A) m in
      pa_ainv A m md -> mem_inv (cl_segs LPA) v ->
      a0 = wz p -> a1 = wz n -> 1 <= n < REQ_MAX -> n <= NREQ_CAP -> p <> 0 -> as_live A p = Some old ->
      as_livebytes A + n <= LIVE_MAX -> as_nlive A + 1 <= NLIVE_MAX -> (n < 16 -> 1 <= as_tinycred A) ->
      (kMaxPrimaryUser < n -> 1 <= as_seccred A) -> prim_cost n <= as_primcred A (* [comment removed for export] *) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites LPA) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A') m' in
          pa_ainv A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          (forall ff, as_fframe A' ff = as_fframe A ff) ->
          as_tinycred A' = as_tinycred A - (if Z.ltb n 16 then 1 else 0) -> as_nlive A' = as_nlive A ->
          (r <> 0 /\ r <> p /\ as_live A r = None /\ as_live A' r = Some n /\ as_live A' p = None /\
               (forall q, q <> r -> q <> p -> as_live A' q = as_live A q) /\
               as_livebytes A' = as_livebytes A + n - old /\
               (forall i, 0 <= i < Z.min n old -> v' (wz (r + i)) = v (wz (p + i))) /\
               frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK (newblk p old) (newblk r n)
                        (aview_of (pa_hull A) m) v' /\
               as_seccred A' = as_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) /\
               as_primcred A' = as_primcred A - prim_cost n (* [comment removed for export] *)) ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' (seg_rom (cl_segs LPA))) md') T) ->
      srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_realloc_pc LPA) fc None m (seg_rom (cl_segs LPA))) md) T.

(* [comment removed for export] *)
Lemma pa_malloc_15_of_16 : pa_malloc_obligation16 -> pa_malloc_obligation.
Proof.
  intros H16. unfold pa_malloc_obligation. intros until T. cbv zeta. intros AINV MI A0 N1 NC LB NL TC SC PC TP SP RA SITE S0C CE MAP K.
  eapply H16; try eassumption. cbv zeta. intros. eapply K; try eassumption. right. assumption.
Qed.

Lemma pa_calloc_15_of_16 : pa_calloc_obligation16 -> pa_calloc_obligation.
Proof.
  intros H16. unfold pa_calloc_obligation. intros until T. cbv zeta. intros AINV MI A0 A1 C1 C2 C3 NC LB NL TC SC PC TP SP RA SITE S0C CE MAP K.
  eapply H16; try eassumption. cbv zeta. intros. eapply K; try eassumption. right. assumption.
Qed.

Lemma pa_realloc_15_of_16 : pa_realloc_obligation16 -> pa_realloc_obligation.
Proof.
  intros H16. unfold pa_realloc_obligation. intros until T. cbv zeta. intros AINV MI A0 A1 N1 NC PN LV LB NL TC SC PC TP SP RA SITE S0C CE MAP K.
  eapply H16; try eassumption. cbv zeta. intros. eapply K; try eassumption. right. assumption.
Qed.

End Obligations16.
