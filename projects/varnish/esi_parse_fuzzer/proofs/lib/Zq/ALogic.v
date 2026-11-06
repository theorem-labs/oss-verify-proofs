(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Export AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Export LayoutPA AInv ALogic1 ALogic2 ALogic3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section Obligations.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Context {DR : DepotRep}.
#[local] Notation WF := (WF AL_pboth).   (* [comment removed for export] *)

Definition pa_malloc_obligation : Prop :=
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
          (   (r = 0 /\ (forall q, as_live A' q = as_live A q) /\ as_livebytes A' = as_livebytes A /\
               as_nlive A' = as_nlive A /\ as_seccred A' = as_seccred A /\ as_primcred A' = as_primcred A (* [comment removed for export] *))
           \/ (r <> 0 /\ as_live A r = None /\ as_live A' r = Some n /\
               (forall q, q <> r -> as_live A' q = as_live A q) /\
               as_livebytes A' = as_livebytes A + n /\ as_nlive A' = as_nlive A + 1 /\
               as_seccred A' = as_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) /\
               as_primcred A' = as_primcred A - prim_cost n (* [comment removed for export] *))) ->
          frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK nowhere (newblk r n)
                   (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' (seg_rom (cl_segs LPA))) md') T) ->
      srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_malloc_pc LPA) fc None m (seg_rom (cl_segs LPA))) md) T.

Definition pa_free_obligation : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n0 : Z) (T : TSet),
      let v := aview_of (pa_hull A) m in
      pa_ainv A m md -> mem_inv (cl_segs LPA) v ->
      a0 = wz p -> ((p = 0 /\ n0 = 0) \/ as_live A p = Some n0) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites LPA) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A') m' in
          pa_ainv A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          hull_le (pa_hull A) (pa_hull A') \/ True ->     (* [comment removed for export] *)
          (forall ff, as_fframe A' ff = as_fframe A ff) ->
          as_live A' p = None -> (forall q, q <> p -> as_live A' q = as_live A q) ->
          as_livebytes A' = as_livebytes A - n0 -> as_tinycred A' = as_tinycred A -> as_seccred A' = as_seccred A ->
          as_primcred A' = as_primcred A (* [comment removed for export] *) ->
          as_nlive A' = as_nlive A - (if Z.eqb p 0 then 0 else 1) ->
          (forall i, 0 <= i < 4 -> mrd (cl_segs LPA) v' (wz (cl_errno LPA + i)) = mrd (cl_segs LPA) v (wz (cl_errno LPA + i))) ->
          frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK (newblk p n0) nowhere
                   (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' (seg_rom (cl_segs LPA))) md') T) ->
      srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_free_pc LPA) fc None m (seg_rom (cl_segs LPA))) md) T.

Definition pa_calloc_obligation : Prop :=
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
          (   (r = 0 /\ (forall q, as_live A' q = as_live A q) /\ as_livebytes A' = as_livebytes A /\
               as_nlive A' = as_nlive A /\ as_seccred A' = as_seccred A /\ as_primcred A' = as_primcred A (* [comment removed for export] *))
           \/ (r <> 0 /\ as_live A r = None /\ as_live A' r = Some (cnt * sz) /\
               (forall q, q <> r -> as_live A' q = as_live A q) /\ all_zero v' r (cnt * sz) /\
               as_livebytes A' = as_livebytes A + cnt * sz /\ as_nlive A' = as_nlive A + 1 /\
               as_seccred A' = as_seccred A - (if Z.ltb kMaxPrimaryUser (cnt * sz) then 1 else 0) /\
               as_primcred A' = as_primcred A - prim_cost (cnt * sz) (* [comment removed for export] *))) ->
          frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK nowhere (newblk r (cnt * sz))
                   (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' (seg_rom (cl_segs LPA))) md') T) ->
      srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_calloc_pc LPA) fc None m (seg_rom (cl_segs LPA))) md) T.

Definition pa_realloc_obligation : Prop :=
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
          (   (* [comment removed for export] *)
              (r = 0 /\ hull_le (pa_hull A) (pa_hull A') /\ (forall q, as_live A' q = as_live A q) /\
               as_livebytes A' = as_livebytes A /\
               bytes_eq v v' p old /\
               frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK nowhere nowhere (aview_of (pa_hull A) m) v' /\
               as_seccred A' = as_seccred A /\ as_primcred A' = as_primcred A (* [comment removed for export] *))
              (* [comment removed for export] *)
           \/ (r <> 0 /\ r <> p /\ as_live A r = None /\ as_live A' r = Some n /\ as_live A' p = None /\
               (forall q, q <> r -> q <> p -> as_live A' q = as_live A q) /\
               as_livebytes A' = as_livebytes A + n - old /\
               (forall i, 0 <= i < Z.min n old -> v' (wz (r + i)) = v (wz (p + i))) /\
               frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK (newblk p old) (newblk r n)
                        (aview_of (pa_hull A) m) v' /\
               as_seccred A' = as_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) /\
               as_primcred A' = as_primcred A - prim_cost n (* [comment removed for export] *))) ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' (seg_rom (cl_segs LPA))) md') T) ->
      srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_realloc_pc LPA) fc None m (seg_rom (cl_segs LPA))) md) T.

Definition pa_smalloc_obligation : Prop :=
    forall (k : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (sz : Z) (T : TSet),
      let v := aview_of (pa_hull A) m in
      pa_ainv A m md -> mem_inv (cl_segs LPA) v ->
      (k = 0 \/ k = 1 \/ k = 7) (* [comment removed for export] *) -> a0 = wz sz -> 0 < sz <= fsize k (* [comment removed for export] *) ->
      (7 <= k -> sz mod 8 = 0) (* [comment removed for export] *) ->
      (forall ff age, as_fframe A ff = Some (k, age) -> Z.of_nat age + 2 < fslots k) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (ff : Z) (A' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A') m' in
          pa_ainv A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          pa_hull A' = pa_hull A -> pa_eager A' = pa_eager A ->
          (forall q, as_live A' q = as_live A q) -> as_livebytes A' = as_livebytes A ->
          as_tinycred A' = as_tinycred A -> as_nlive A' = as_nlive A -> as_seccred A' = as_seccred A -> as_primcred A' = as_primcred A (* [comment removed for export] *) ->
          ff <> 0 -> as_fframe A ff = None -> as_fframe A' ff = Some (k, 0%nat) ->
          (forall g k' age', g <> ff -> as_fframe A g = Some (k', age') ->
              as_fframe A' g = Some (k', if Z.eqb k' k then S age' else age')) ->
          (forall g, g <> ff -> as_fframe A g = None -> as_fframe A' g = None) ->
          all_zero v' (sh ff) (if Z.leb k 6 then fsize k / 8 else sz / 8) ->
          frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK nowhere (frm ff k) (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz ff) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom (cl_segs LPA))) md') T) ->
      srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_smalloc_pc LPA k) fc None m (seg_rom (cl_segs LPA))) md) T.

Definition pa_sfree_obligation : Prop :=
    forall (k : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (ff sz : Z) (age : nat) (T : TSet),
      let v := aview_of (pa_hull A) m in
      pa_ainv A m md -> mem_inv (cl_segs LPA) v ->
      k = 7 (* [comment removed for export] *) -> a0 = wz ff -> a1 = wz sz -> 0 < sz <= fsize k -> (7 <= k -> sz mod 8 = 0) ->
      as_fframe A ff = Some (k, age) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (md' : Model),
          let A' := as_release A ff in
          let v' := aview_of (pa_hull A') m' in
          pa_ainv A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK (frm ff k) nowhere (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom (cl_segs LPA))) md') T) ->
      srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_sfree_pc LPA k) fc None m (seg_rom (cl_segs LPA))) md) T.

(* [comment removed for export] *)
Lemma heap_shadow_below_ceiling : forall A a, WF A -> heap_shadow A a -> a < sh alloc_ceiling.
Proof.
  intros A a W HS. pose proof alloc_ceiling_val as CE. unfold heap_shadow, heap_shadow_ in HS. change (p_sb (a_pl A)) with (a_sb A) in HS.
  destruct HS as [(c & Hc & R)|[(c & Hc & R)|(sc & Hsc & R)]]; cbv zeta in R.
  - pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB.
    (first [ dand11 RB as _ _ _ B4 _ B6 B7 B8 AL MU _ | destruct RB as (_ & _ & _ & B4 & _ & B6 & B7 & B8 & AL & MU & _) ]).
    pose proof (sh_add (region_beg (a_sb A) c) (rg_mapped_user (a_reg A c)) ltac:(apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact AL]) MU) as E.
    pose proof (sh_mono (region_beg (a_sb A) c + rg_mapped_user (a_reg A c)) (@alloc_ceiling Clg - 8) ltac:(unfold kFreeArrayOffset, kRegionSize in *; lia)).
    assert (sh (alloc_ceiling - 8) < sh alloc_ceiling) by (pose proof alloc_ceiling_mod16; unfold sh; lia). lia.
  - pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB.
    (first [ dand12 RB as _ _ _ B4 _ B6 B7 B8 AL _ _ MF | destruct RB as (_ & _ & _ & B4 & _ & B6 & B7 & B8 & AL & _ & _ & MF) ]).
    pose proof (sh_add (region_beg (a_sb A) c + kFreeArrayOffset) (rg_mapped_fa (a_reg A c))
      ltac:(rewrite Z.add_mod by lia; rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) AL); reflexivity) MF) as E.
    pose proof (sh_mono (region_beg (a_sb A) c + kFreeArrayOffset + rg_mapped_fa (a_reg A c)) (@alloc_ceiling Clg - 8) ltac:(unfold kFreeArrayOffset, kRegionSize in *; lia)).
    assert (sh (alloc_ceiling - 8) < sh alloc_ceiling) by (pose proof alloc_ceiling_mod16; unfold sh; lia). lia.
  - (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR_3; dand5 dR_3 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A sc W Hsc) as (B1 & B2 & B3 & B4 & B5) ]). pose proof (map_size_page (cs_n sc)) as MP.
    pose proof (sh_add (cs_map sc) (map_size (cs_n sc)) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2])
      (mod0_down _ kPageSize 8 ltac:(exists 512; reflexivity) MP)) as E.
    pose proof (sh_mono (cs_map sc + map_size (cs_n sc)) (alloc_ceiling - 8)).
    assert (sh (alloc_ceiling - 8) < sh alloc_ceiling) by (pose proof alloc_ceiling_mod16; unfold sh; lia).
    assert (MS8 : map_size (cs_n sc) mod 8 = 0) by (apply (mod0_down _ kPageSize 8 ltac:(exists 512; reflexivity) MP)).
    assert (cs_map sc + map_size (cs_n sc) <= alloc_ceiling - 8 \/ cs_map sc + map_size (cs_n sc) = alloc_ceiling).
    { assert (C8 : alloc_ceiling mod 8 = 0) by (apply (mod0_down _ 16 8 ltac:(exists 2; reflexivity) alloc_ceiling_mod16)).
      assert (S8 : (cs_map sc + map_size (cs_n sc)) mod 8 = 0).
      { rewrite Z.add_mod by lia. rewrite (mod0_down _ 4096 8 ltac:(exists 512; reflexivity) B2), MS8. reflexivity. }
      pose proof (Z.div_mod (cs_map sc + map_size (cs_n sc)) 8 ltac:(lia)). pose proof (Z.div_mod alloc_ceiling 8 ltac:(lia)). lia. }
    destruct H1 as [LE|EQ]; [specialize (H LE); lia| rewrite EQ in E; lia].
Qed.

Lemma asI_owned_not_stack_shadow : forall A m md a, pa_ainv A m md ->
  sh alloc_ceiling <= a < kHighMemBeg -> ~ pa_owned A a.
Proof.
  intros A m md a AI R OW. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE.
  assert (SC : 0x10006fef8000 <= sh alloc_ceiling) by (unfold sh, kShadowOffset; lia).
  destruct OW as [[S|[[(IR & _ & _)|[HS|[FS _]]]|[_ NV]]]|IS].
  - pose proof (pa_static_low a S). unfold kHighMemBeg in R. clear S. lia.
  - (first [ dex2 IR as b s; destruct IR as [Hin Hab] | dand4 IR as b s Hin Hab | destruct IR as (b & s & Hin & Hab) ]). pose proof (runtime_maps_range A b s a W Hin Hab). cbn [al_image_lo al_image_hi AL_pboth] in H.
    unfold kHighMemBeg, kLowShadowMapBeg in *. lia.
  - pose proof (heap_shadow_below_ceiling A a W HS). lia.
  - unfold a_fs in *. (first [ pose proof ((place_fs A W)) as dR_5; dand3 dR_5 as F1 F2 F3 | pose proof (place_fs A W) as (F1 & F2 & F3) ]). unfold a_fs in F1, F2, F3.
    pose proof (sh_mono (p_fs (a_pl A) + kFakeStackBytes) (@alloc_ceiling Clg) F2).
    assert (E : sh (p_fs (a_pl A) + kFakeStackBytes) = sh (p_fs (a_pl A)) + kFakeStackBytes / 8).
    { apply sh_add; [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact F3] | reflexivity]. }
    lia.
  - (* [comment removed for export] *)
    apply NV. exists alloc_ceiling, (2^47 - alloc_ceiling). split; [unfold VIS0; cbn [In]; do 13 right; left; reflexivity|].
    replace (alloc_ceiling + (2 ^ 47 - alloc_ceiling)) with (2 ^ 47) by lia. change (2 ^ 47 / 8) with 17592186044416.
    unfold sh, kShadowOffset, kHighMemBeg in *. lia.
  - unfold pa_image_shadow in IS.
    assert (sh 0x60a000 = 0x800b9400) by reflexivity. lia.
Qed.

(* [comment removed for export] *)
Definition pasan_AsanAlloc
  (Hmalloc : pa_malloc_obligation) (Hfree : pa_free_obligation) (Hcalloc : pa_calloc_obligation)
  (Hrealloc : pa_realloc_obligation) (Hsmalloc : pa_smalloc_obligation) (Hsfree : pa_sfree_obligation) : AsanAlloc LPA :=
  {| AS := AState; a_live := as_live; a_frame := as_fframe; a_livebytes := as_livebytes; a_tinycred := as_tinycred; a_seccred := as_seccred; a_primcred := as_primcred (* [comment removed for export] *); a_nlive := as_nlive;
     ahull := pa_hull; alhull := pa_lhull; aeager := pa_eager; ainv := pa_ainv; owned := pa_owned;   (* [comment removed for export] *)
     as_static_owned := asI_static_owned;
     as_static_where := asI_static_where; as_shared_where := asI_shared_where; as_shared_not_static := asI_shared_not_static;
     as_errno_where := asI_errno_where; as_errno_not_static := asI_errno_not_static; as_layout_order := asI_layout_order;
     as_ro_addr_iff := asI_ro_addr_iff; as_seg_rom_outside := asI_seg_rom_outside; as_find_segment_outside := asI_find_segment_outside;
     as_minv := asI_minv; as_hull_segs := asI_hull_segs; as_wx := asI_wx; as_image_visible := asI_image_visible;
     as_shadow_visible := asI_shadow_visible; as_consts := asI_consts; as_owned_where := asI_owned_where;
     as_owned_not_stack_shadow := asI_owned_not_stack_shadow;
     as_live_ok := asI_live_ok; as_live_primary_high := asI_live_primary_high; as_live_shadow := asI_live_shadow; as_live_disjoint := asI_live_disjoint;
     as_frame_ok := asI_frame_ok; as_frame_blk_disjoint := asI_frame_blk_disjoint; as_frame_disjoint := asI_frame_disjoint;
     as_sframe_flag := asI_sframe_flag;
     a_release := as_release; as_release_spec := asI_release_spec;
     AIface.as_frame := asI_frame; as_md_frame := asI_md_frame;
     as_malloc_cps := Hmalloc; as_free_cps := Hfree; as_calloc_cps := Hcalloc; as_realloc_cps := Hrealloc;
     as_smalloc_cps := Hsmalloc; as_sfree_cps := Hsfree |}.

End Obligations.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a_virgin (A : AState) (c : Z) : Prop := a_reg A c = region_zero /\ pk_chunks (a_cache A c) = [].

(* [comment removed for export] *)
(* [comment removed for export] *)
