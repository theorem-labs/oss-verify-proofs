(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section CoreDefsF.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
Definition dealloc_entry_ms (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p stkobj : Z) : machine_state :=
  MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz 0xb1558) (wz p) a2 a3 (wz stkobj) (wz 1) a6 a7
          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x36d68) fc None m (seg_rom (cl_segs LPA)).

(* [comment removed for export] *)
Definition dealloc_core_pre (rac spd tp : word) (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z) : Prop :=
  let v := aview_of (pa_hull A) m in
  @pa_ainv _ DepotRepL A m md /\ mem_inv (cl_segs LPA) v /\
  ((p = 0 /\ n0 = 0) \/ as_live A p = Some n0) /\
  (* [comment removed for export] *)
  a_ia_inited A = true /\
  tp = cl_tp LPA /\
  (* [comment removed for export] *)
  alloc_ceiling <= lo /\ lo <= bv_unsigned spd - 4096 /\ bv_unsigned spd <= hi /\ hi <= 2^47 /\
  bv_unsigned spd mod 16 = 0 /\ bv_unsigned rac mod 2 = 0 /\
  stk (cl_segs LPA) v lo (bv_unsigned spd) /\ mapped v (bv_unsigned spd) (hi - bv_unsigned spd) /\
  (* [comment removed for export] *)
  bv_unsigned spd <= stkobj /\ stkobj + 2064 <= hi /\
  ro_cells (cl_segs LPA) v stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))] /\
  bytes_at (cl_segs LPA) v (stkobj + 16) (u64s (map (Z_to_bv 64) key)) /\
  In key (p_dkeys (a_pl A)) /\ Forall (fun w => 0 <= w < 2^64) key.

(* [comment removed for export] *)
Definition dealloc_core_K (rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (md : Model) (A : AState) (p n0 lo hi : Z) (T : TSet) : Prop :=
  forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AState) (m' : mem) (md' : Model),
    let v := aview_of (pa_hull A) m in let v' := aview_of (pa_hull A') m' in
    @pa_ainv _ DepotRepL A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
    (forall ff, as_fframe A' ff = as_fframe A ff) ->
    a_pl A' = a_pl A ->
    as_live A' p = None -> (forall q, q <> p -> as_live A' q = as_live A q) ->
    as_livebytes A' = as_livebytes A - n0 -> as_tinycred A' = as_tinycred A -> as_seccred A' = as_seccred A ->
    as_primcred A' = as_primcred A (* [comment removed for export] *) ->
    as_nlive A' = as_nlive A - (if Z.eqb p 0 then 0 else 1) ->
    (* [comment removed for export] *)
    (forall c, c <> kQuarantineBatchClass -> a_virgin A c -> a_virgin A' c) ->
    (forall i, 0 <= i < 4 -> mrd (cl_segs LPA) v' (wz (cl_errno LPA + i)) = mrd (cl_segs LPA) v (wz (cl_errno LPA + i))) ->
    frame_ok LPA (pa_owned A) (pa_owned A') hi (hi - lo) (newblk p n0) nowhere v v' ->
    (* [comment removed for export] *)
    (forall a, bv_unsigned spd <= a < hi -> v' (wz a) = v (wz a)) ->
    stk (cl_segs LPA) v' lo (bv_unsigned spd) ->
    srealizes (cl_segs LPA) (mkCfg (MS (mkR rac spd gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m' (seg_rom (cl_segs LPA))) md') T.

Definition dealloc_core_cps : Prop :=
  forall (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z) (T : TSet),
    dealloc_core_pre rac spd tp m md A p n0 stkobj lo hi key ->
    dealloc_core_K rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 lo hi T ->
    srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.

End CoreDefsF.
