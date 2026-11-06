(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section AI16.
Context {Clg : Ceiling} {AI : AsanAlloc LPA}.
Let L := LPA.
Let segs := cl_segs LPA.
Let rom := seg_rom (cl_segs LPA).

  Definition as_malloc_cps16_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (n : Z) (T : TSet),
      let v := aview_of (ahull A) m in
      ainv A m md -> mem_inv segs v ->
      a0 = wz n -> 1 <= n < REQ_MAX -> n <= NREQ_CAP ->
      a_livebytes A + n <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX -> (n < 16 -> 1 <= a_tinycred A) ->
      (kMaxPrimaryUser < n -> 1 <= a_seccred A) -> prim_cost n <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites L) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview_of (ahull A') m' in
          ainv A' m' md' -> mem_inv segs v' -> amd_frame md md' ->
          hull_le (ahull A) (ahull A') ->
          (forall ff, a_frame A' ff = a_frame A ff) ->
          a_tinycred A' = a_tinycred A - (if Z.ltb n 16 then 1 else 0) ->
          (r <> 0 /\ a_live A r = None /\ a_live A' r = Some n /\
               (forall q, q <> r -> a_live A' q = a_live A q) /\
               a_livebytes A' = a_livebytes A + n /\ a_nlive A' = a_nlive A + 1 /\
               a_seccred A' = a_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) /\
               a_primcred A' = a_primcred A - prim_cost n (* [comment removed for export] *)) ->
          frame_ok LPA (owned A) (owned A') (bv_unsigned sp) ASTK nowhere (newblk r n)
                   (aview_of (ahull A) m) v' ->
          srealizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' rom) md') T) ->
      srealizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_malloc_pc L) fc None m rom) md) T.

  Definition as_calloc_cps16_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (cnt sz : Z) (T : TSet),
      let v := aview_of (ahull A) m in
      ainv A m md -> mem_inv segs v ->
      a0 = wz cnt -> a1 = wz sz -> 0 <= cnt < REQ_MAX -> 0 <= sz < REQ_MAX -> 1 <= cnt * sz < REQ_MAX -> cnt * sz <= NREQ_CAP ->
      a_livebytes A + cnt * sz <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX -> (cnt * sz < 16 -> 1 <= a_tinycred A) ->
      (kMaxPrimaryUser < cnt * sz -> 1 <= a_seccred A) -> prim_cost (cnt * sz) <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites L) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview_of (ahull A') m' in
          ainv A' m' md' -> mem_inv segs v' -> amd_frame md md' ->
          hull_le (ahull A) (ahull A') ->
          (forall ff, a_frame A' ff = a_frame A ff) ->
          a_tinycred A' = a_tinycred A - (if Z.ltb (cnt * sz) 16 then 1 else 0) ->
          (r <> 0 /\ a_live A r = None /\ a_live A' r = Some (cnt * sz) /\
               (forall q, q <> r -> a_live A' q = a_live A q) /\ all_zero v' r (cnt * sz) /\
               a_livebytes A' = a_livebytes A + cnt * sz /\ a_nlive A' = a_nlive A + 1 /\
               a_seccred A' = a_seccred A - (if Z.ltb kMaxPrimaryUser (cnt * sz) then 1 else 0) /\
               a_primcred A' = a_primcred A - prim_cost (cnt * sz) (* [comment removed for export] *)) ->
          frame_ok LPA (owned A) (owned A') (bv_unsigned sp) ASTK nowhere (newblk r (cnt * sz))
                   (aview_of (ahull A) m) v' ->
          srealizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' rom) md') T) ->
      srealizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_calloc_pc L) fc None m rom) md) T.

  Definition as_realloc_cps16_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (p n old : Z) (T : TSet),
      let v := aview_of (ahull A) m in
      ainv A m md -> mem_inv segs v ->
      a0 = wz p -> a1 = wz n -> 1 <= n < REQ_MAX -> n <= NREQ_CAP -> p <> 0 -> a_live A p = Some old ->
      a_livebytes A + n <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX -> (n < 16 -> 1 <= a_tinycred A) ->
      (kMaxPrimaryUser < n -> 1 <= a_seccred A) -> prim_cost n <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites L) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview_of (ahull A') m' in
          ainv A' m' md' -> mem_inv segs v' -> amd_frame md md' ->
          (forall ff, a_frame A' ff = a_frame A ff) ->
          a_tinycred A' = a_tinycred A - (if Z.ltb n 16 then 1 else 0) -> a_nlive A' = a_nlive A ->
          (* [comment removed for export] *)
          (r <> 0 /\ r <> p /\ a_live A r = None /\ a_live A' r = Some n /\ a_live A' p = None /\
               (forall q, q <> r -> q <> p -> a_live A' q = a_live A q) /\
               a_livebytes A' = a_livebytes A + n - old /\
               (forall i, 0 <= i < Z.min n old -> v' (wz (r + i)) = v (wz (p + i))) /\
               frame_ok LPA (owned A) (owned A') (bv_unsigned sp) ASTK (newblk p old) (newblk r n)
                        (aview_of (ahull A) m) v' /\
               a_seccred A' = a_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) /\
               a_primcred A' = a_primcred A - prim_cost n (* [comment removed for export] *)) ->
          srealizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' rom) md') T) ->
      srealizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_realloc_pc L) fc None m rom) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Class AsanAlloc16 := {
    as_malloc_cps16 : as_malloc_cps16_stmt;
    as_calloc_cps16 : as_calloc_cps16_stmt;
    as_realloc_cps16 : as_realloc_cps16_stmt }.
End AI16.
