(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section CoreDefs.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
Definition alloc_entry_ms (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (n stkobj canfill : Z) : machine_state :=
  MS (mkR rac spa gp tp t0 t1 t2 s0 s1 (wz 0xb1d58) (wz n) (wz 8) (wz stkobj) (wz 1) (wz canfill) a6 a7
          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x3719c) fc None m (seg_rom (cl_segs LPA)).

(* [comment removed for export] *)
Definition alloc_core_pre (rac spa tp : word) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) : Prop :=
  let v := aview_of (pa_hull A) m in
  @pa_ainv _ DepotRepL A m md /\ mem_inv (cl_segs LPA) v /\
  1 <= n < REQ_MAX /\ n <= NREQ_CAP /\
  as_livebytes A + n <= LIVE_MAX /\ as_nlive A + 1 <= NLIVE_MAX /\ (n < 16 -> 1 <= as_tinycred A) /\
  (kMaxPrimaryUser < n -> 1 <= as_seccred A) /\ prim_cost n <= as_primcred A (* [comment removed for export] *) /\
  0 <= canfill <= 1 /\ tp = cl_tp LPA /\
  (* [comment removed for export] *)
  alloc_ceiling <= lo /\ lo <= bv_unsigned spa - 4096 /\ bv_unsigned spa <= hi /\ hi <= 2^47 /\
  bv_unsigned spa mod 16 = 0 /\ bv_unsigned rac mod 2 = 0 /\
  stk (cl_segs LPA) v lo (bv_unsigned spa) /\ mapped v (bv_unsigned spa) (hi - bv_unsigned spa) /\
  (* [comment removed for export] *)
  bv_unsigned spa <= stkobj /\ stkobj + 2064 <= hi /\
  ro_cells (cl_segs LPA) v stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))] /\
  bytes_at (cl_segs LPA) v (stkobj + 16) (u64s (map (Z_to_bv 64) key)) /\
  In key (p_dkeys (a_pl A)) /\ Forall (fun w => 0 <= w < 2^64) key.

(* [comment removed for export] *)
Definition alloc_core_K0v (rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (md : Model) (A : AState) (n lo hi : Z) (T0 : TSet) : Prop :=
  forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AState) (m' : mem) (md' : Model),
    let v := aview_of (pa_hull A) m in let v' := aview_of (pa_hull A') m' in
    @pa_ainv _ DepotRepL A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
    hull_le (pa_hull A) (pa_hull A') ->
    (forall ff, as_fframe A' ff = as_fframe A ff) -> a_pl A' = a_pl A -> a_ia_inited A' = a_ia_inited A ->
    (forall c, a_virgin A c -> (kMaxPrimaryUser < n \/ c <> class_of n) -> a_virgin A' c) ->
    (forall q, as_live A' q = as_live A q) -> as_livebytes A' = as_livebytes A ->
    as_tinycred A' = as_tinycred A - (if Z.ltb n 16 then 1 else 0) -> as_nlive A' = as_nlive A -> as_seccred A' = as_seccred A ->
    as_primcred A' = as_primcred A (* [comment removed for export] *) ->
    frame_ok LPA (pa_owned A) (pa_owned A') hi (hi - lo) nowhere nowhere v v' ->
    (forall i, 0 <= i < 4 -> mrd (cl_segs LPA) v' (wz (cl_errno LPA + i)) = mrd (cl_segs LPA) v (wz (cl_errno LPA + i))) ->
    (forall a, bv_unsigned spa <= a < hi -> v' (wz a) = v (wz a)) ->
    stk (cl_segs LPA) v' lo (bv_unsigned spa) ->
    srealizes (cl_segs LPA) (mkCfg (MS (mkR rac spa gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7'
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m' (seg_rom (cl_segs LPA))) md') T0.

(* [comment removed for export] *)
Definition alloc_core_K1v (rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (md : Model) (A : AState) (n canfill lo hi : Z) (T1 : TSet) : Prop :=
  forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AState) (m' : mem) (md' : Model),
    let v := aview_of (pa_hull A) m in let v' := aview_of (pa_hull A') m' in
    @pa_ainv _ DepotRepL A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
    hull_le (pa_hull A) (pa_hull A') ->
    (forall ff, as_fframe A' ff = as_fframe A ff) -> a_pl A' = a_pl A -> a_ia_inited A' = a_ia_inited A ->
    (forall c, a_virgin A c -> (kMaxPrimaryUser < n \/ c <> class_of n) -> a_virgin A' c) ->
    r <> 0 -> as_live A r = None -> as_live A' r = Some n -> (forall q, q <> r -> as_live A' q = as_live A q) ->
    as_livebytes A' = as_livebytes A + n ->
    as_tinycred A' = as_tinycred A - (if Z.ltb n 16 then 1 else 0) -> as_nlive A' = as_nlive A + 1 ->
    as_seccred A' = as_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) ->
    as_primcred A' = as_primcred A - prim_cost n (* [comment removed for export] *) ->
    (* [comment removed for export] *)
    (canfill = 0 -> kMaxPrimaryUser < n -> all_zero v' r n) ->
    (* [comment removed for export] *)
    (n <= kMaxPrimaryUser <-> p_sb (a_pl A) <= r < p_sb (a_pl A) + kSpaceSize) ->
    frame_ok LPA (pa_owned A) (pa_owned A') hi (hi - lo) nowhere (newblk r n) v v' ->
    (forall i, 0 <= i < 4 -> mrd (cl_segs LPA) v' (wz (cl_errno LPA + i)) = mrd (cl_segs LPA) v (wz (cl_errno LPA + i))) ->
    (forall a, bv_unsigned spa <= a < hi -> v' (wz a) = v (wz a)) ->
    stk (cl_segs LPA) v' lo (bv_unsigned spa) ->
    srealizes (cl_segs LPA) (mkCfg (MS (mkR rac spa gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m' (seg_rom (cl_segs LPA))) md') T1.

(* [comment removed for export] *)
Definition alloc_core_cps1 : Prop :=
  forall (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T1 : TSet),
    alloc_core_pre rac spa tp m md A n canfill stkobj lo hi key ->
    alloc_core_K1v rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T1 ->
    srealizes (cl_segs LPA) (mkCfg (alloc_entry_ms rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n stkobj canfill) md) T1.

(* [comment removed for export] *)
Definition alloc_core_K (rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (md : Model) (A : AState) (n canfill lo hi : Z) (T : TSet) : Prop :=
  forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AState) (m' : mem) (md' : Model),
    let v := aview_of (pa_hull A) m in let v' := aview_of (pa_hull A') m' in
    @pa_ainv _ DepotRepL A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
    hull_le (pa_hull A) (pa_hull A') ->
    (forall ff, as_fframe A' ff = as_fframe A ff) -> a_pl A' = a_pl A -> a_ia_inited A' = a_ia_inited A ->
    (forall c, a_virgin A c -> (kMaxPrimaryUser < n \/ c <> class_of n) -> a_virgin A' c) ->
    as_tinycred A' = as_tinycred A - (if Z.ltb n 16 then 1 else 0) ->
    (   (r = 0 /\ (forall q, as_live A' q = as_live A q) /\ as_livebytes A' = as_livebytes A /\
         as_nlive A' = as_nlive A /\ as_seccred A' = as_seccred A /\ as_primcred A' = as_primcred A (* [comment removed for export] *))
     \/ (r <> 0 /\ as_live A r = None /\ as_live A' r = Some n /\
         (forall q, q <> r -> as_live A' q = as_live A q) /\
         as_livebytes A' = as_livebytes A + n /\ as_nlive A' = as_nlive A + 1 /\
         as_seccred A' = as_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) /\
         as_primcred A' = as_primcred A - prim_cost n (* [comment removed for export] *) /\
         (canfill = 0 -> kMaxPrimaryUser < n -> all_zero v' r n) /\
         (n <= kMaxPrimaryUser <-> p_sb (a_pl A) <= r < p_sb (a_pl A) + kSpaceSize))) ->
    frame_ok LPA (pa_owned A) (pa_owned A') hi (hi - lo) nowhere (newblk r n) v v' ->
    (forall i, 0 <= i < 4 -> mrd (cl_segs LPA) v' (wz (cl_errno LPA + i)) = mrd (cl_segs LPA) v (wz (cl_errno LPA + i))) ->
    (forall a, bv_unsigned spa <= a < hi -> v' (wz a) = v (wz a)) ->
    stk (cl_segs LPA) v' lo (bv_unsigned spa) ->
    srealizes (cl_segs LPA) (mkCfg (MS (mkR rac spa gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m' (seg_rom (cl_segs LPA))) md') T.

Definition alloc_core_cps : Prop :=
  forall (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T : TSet),
    alloc_core_pre rac spa tp m md A n canfill stkobj lo hi key ->
    alloc_core_K rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T ->
    srealizes (cl_segs LPA) (mkCfg (alloc_entry_ms rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n stkobj canfill) md) T.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End CoreDefs.
