(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Mem Cells Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition ASEGS := cl_segs LPA.

(* [comment removed for export] *)
Definition zero_at (m : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> m (wz (a + i)) = Some (Z_to_bv 8 0).
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section A0.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.

  (* [comment removed for export] *)
  Definition A0_of (P : aplace) (k1 : list Z) : AState :=
    mkA P (fun _ => region_zero) false (fun _ => PCc []) ∅ [] [] (SR [] 0) [k1] (fun _ => 0) ∅ false false TINYCRED0
        [] SECCRED0 [] PRIMCRED0 (fun _ => []).   (* [comment removed for export] *)

  Definition a0_hull (P : aplace) (k1 : list Z) : hull := pa_hull (A0_of P k1).     (* [comment removed for export] *)
  Definition a0_lhull (P : aplace) (k1 : list Z) : hull := pa_lhull (A0_of P k1).   (* [comment removed for export] *)
  Definition a0_eager (P : aplace) (k1 : list Z) : Z := pa_eager (A0_of P k1).      (* [comment removed for export] *)
End A0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record a0_depot_raw (P : aplace) (k1 : list Z) (FULL : mem) : Prop := {
  ad_k1      : (1 <= length k1 <= 255)%nat /\ Forall (fun w => 0 <= w < 2^64) k1;
  (* [comment removed for export] *)
  ad_tab     : forall b, 0 <= b < 2^20 ->
                 u32_at ASEGS FULL (al_theDepot AL_pasan + 4 * b) (if b =? depot_bucket k1 then 1 else 0);
  ad_nuniq   : u32_at ASEGS FULL (al_depot_n_uniq_ids AL_pasan) 1;                       (* [comment removed for export] *)
  ad_map1_0  : u64_at ASEGS FULL (al_depot_nodes_map1 AL_pasan) (p_nodes0 P);            (* [comment removed for export] *)
  ad_map1_j  : forall j, 1 <= j < kDepotNodesL1 -> u64_at ASEGS FULL (al_depot_nodes_map1 AL_pasan + 8 * j) 0;
  (* [comment removed for export] *)
  ad_node1   : u64_at ASEGS FULL (p_nodes0 P + 16) (depot_hashC k1) /\ u32_at ASEGS FULL (p_nodes0 P + 24) 0 /\
               u32_at ASEGS FULL (p_nodes0 P + 28) 1;
  ad_nodes_zero : zero_at FULL (p_nodes0 P) 16 /\ zero_at FULL (p_nodes0 P + 32) (kDepotNodesBlock - 32);
  (* [comment removed for export] *)
  ad_ss_total  : u64_at ASEGS FULL (al_stackStore AL_pasan) (1 + Z.of_nat (length k1));
  ad_ss_alloc  : u64_at ASEGS FULL (al_stackStore AL_pasan + 8) kStackStoreBlockBytes;   (* [comment removed for export] *)
  ad_ss_block0 : u64_at ASEGS FULL (al_stackStore AL_pasan + 16) (p_frames0 P) /\
                 u32_at ASEGS FULL (al_stackStore AL_pasan + 24) (1 + Z.of_nat (length k1)) /\
                 u32_at ASEGS FULL (al_stackStore AL_pasan + 28) 0;
  ad_frames    : u64_at ASEGS FULL (p_frames0 P) (Z.of_nat (length k1)) /\
                 (forall t w, nth_error k1 t = Some w -> u64_at ASEGS FULL (p_frames0 P + 8 * (1 + Z.of_nat t)) w) /\
                 zero_at FULL (p_frames0 P + 8 * (1 + Z.of_nat (length k1))) (kStackStoreBlockBytes - 8 * (1 + Z.of_nat (length k1)));
  (* [comment removed for export] *)
  ad_blocks  : mapped FULL (p_nodes0 P) kDepotNodesBlock /\ mapped FULL (p_frames0 P) kStackStoreBlockBytes
}.

(* [comment removed for export] *)
Definition depot_init_ok (DR : DepotRep) : Prop :=
  forall P k1 (m : mem), a0_depot_raw P k1 m -> @depot_rep DR AL_pasan ASEGS [k1] (p_nodes0 P) (p_frames0 P) m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Record a0_raw (P : aplace) (k1 : list Z) (sp0 : Z) (FULL : mem) (md : Model) : Prop := {
  (* [comment removed for export] *)
  ar0_sp0    : p_sp0 P = sp0;
  ar0_place  : wf_place AL_pasan P;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  ar0_consts : consts_repr_ LPA AL_pasan P FULL;
  (* [comment removed for export] *)
  ar0_locks  : locks_repr_ LPA AL_pasan P [] FULL;     (* [comment removed for export] *)
  (* [comment removed for export] *)
  ar0_ri_zero : zero_at FULL (p_ri P) 4096;
  (* [comment removed for export] *)
  ar0_thr_zero : zero_at FULL (p_thr P + 80) (2800 - 80);
  ar0_thr_map  : mapped FULL (p_thr P) 4096 /\ mapped FULL (p_ctx P) 0x10000;
  (* [comment removed for export] *)
  ar0_qglobal_zero : fill_at ASEGS FULL (al_instance AL_pasan + off_q_cache_list_size) 32 0;     (* [comment removed for export] *)
  ar0_sec_zero : u64_at ASEGS FULL (al_instance AL_pasan + off_sec_n_reserved) 0 /\
                 u64_at ASEGS FULL (al_instance AL_pasan + off_sec_n_chunks) 0;
  (* [comment removed for export] *)
  ar0_ia     : u8_at ASEGS FULL (al_internal_alloc_inited AL_pasan) 0 /\ fill_at ASEGS FULL (al_internal_allocator_inst AL_pasan) 0x81030 0;
  (* [comment removed for export] *)
  ar0_depot  : a0_depot_raw P k1 FULL;
  (* [comment removed for export] *)
  ar0_k1     : In k1 (p_dkeys P);
  (* [comment removed for export] *)
  ar0_fs_hints : zero_at FULL (p_fs P) 88;
  ar0_fs_log   : u64_at ASEGS FULL (p_fs P + 88) kFakeStackSizeLog /\ u8_at ASEGS FULL (p_fs P + 96) 0;
  ar0_fs_flags : zero_at FULL (p_fs P + kFakeFlagsOffset) (kFakeFramesOffset - kFakeFlagsOffset);
  ar0_fs_map   : mapped FULL (p_fs P) kFakeStackBytes /\ mapped FULL (sh (p_fs P)) (kFakeStackBytes / 8);
  (* [comment removed for export] *)
  ar0_maps   : mapped FULL (sp0 - 0x800000) 0x800000;
  (* [comment removed for export] *)
  ar0_stkshadow_map : mapped FULL (fst stack_shadow_iv) (snd stack_shadow_iv);
  ar0_imgshadow_map : mapped FULL 0x7fffa000 0xbf400;
  (* [comment removed for export] *)
  ar0_hidden : forall z, in_shadow_maps z -> ~ in_vis_shadow (VIS0 P) z -> FULL (wz z) = Some (Z_to_bv 8 0);
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ar0_extra : wf_extra LPA pa_site_pcs P;
  (* [comment removed for export] *)
  ar0_ledger : aledger_ AL_pasan P (fun _ => region_zero) (SR [] 0) md;   (* [comment removed for export] *)
  ar0_bigmaps : wf_bigmaps_ P (SR [] 0);
  (* [comment removed for export] *)
  ar0_minv   : MInv (a0_hull P k1) (a0_lhull P k1) (a0_eager P k1) md;   (* [comment removed for export] *)
  ar0_halted : m_halted md = None;
  (* [comment removed for export] *)
  ar0_reserved : vm_reserved (m_vmmaps md) = segments_reserved ASEGS;       (* [comment removed for export] *)
  (* [comment removed for export] *)
  ar0_gap : In (Z_to_bv 64 kShadowGapBeg, Z_to_bv 64 (kHighShadowMapBeg - kShadowGapBeg)) (vm_maps (m_vmmaps md));
  (* [comment removed for export] *)
  ar0_vmmaps : exists fog : list (Z * Z),
      Z.of_nat (length fog) <= 2 /\ Forall (fun bs => 0 <= fst bs /\ 0 < snd bs <= 8192 /\ fst bs + snd bs <= 2^47) fog /\
      (forall e, In e (vm_maps (m_vmmaps md)) ->
          let bs := (bv_unsigned (fst e), bv_unsigned (snd e)) in
          In bs (AInv.big_maps_ P (SR [] 0)) \/ In bs fog \/ bs = (kShadowGapBeg, kHighShadowMapBeg - kShadowGapBeg)) /\
      (forall bs, In bs fog -> In (Z_to_bv 64 (fst bs), Z_to_bv 64 (snd bs)) (vm_maps (m_vmmaps md))) /\
      (forall lo hi a, In (lo, hi) (p_extra P) -> lo <= a < hi -> 0 <= a < alloc_ceiling ->
          ~ (kLowShadowMapBeg <= a < kHighMemBeg) ->
          (cl_image_lo LPA <= a < cl_image_hi LPA) \/ in_regions (AInv.big_maps_ P (SR [] 0)) a \/ in_regions fog a)
}.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Facts.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Record a0_facts (sp0 : Z) (A0 : AState) : Prop := {
    (* [comment removed for export] *)
    a0_live   : forall p, as_live A0 p = None;
    a0_frames : forall ff, as_fframe A0 ff = None;
    a0_bytes  : as_livebytes A0 = 0;
    a0_cred   : as_tinycred A0 = TINYCRED0;   (* [comment removed for export] *)
    a0_scred  : as_seccred A0 = SECCRED0;     (* [comment removed for export] *)
    a0_pcred  : as_primcred A0 = PRIMCRED0;   (* [comment removed for export] *)
    a0_nlive  : as_nlive A0 = 0;              (* [comment removed for export] *)
    (* [comment removed for export] *)
    a0_span   : 0 <= p_stk_span (a_pl A0) /\ p_sp0 (a_pl A0) = sp0;
    a0_vis    : forall a,
        (al_image_lo AL_pasan <= a < al_image_hi AL_pasan) \/
        (sp0 - 0x800000 <= a < sp0 + p_stk_span (a_pl A0)) \/
        (sh (al_image_lo AL_pasan) <= a < sh (al_image_hi AL_pasan)) \/
        (fst stack_shadow_iv <= a < fst stack_shadow_iv + snd stack_shadow_iv) (* [comment removed for export] *) ->
        hidc (pa_hull A0) (wz a) = false;
    (* [comment removed for export] *)
    a0_owned  : forall a, pa_owned A0 a ->
           cl_static LPA a
        \/ pa_image_shadow a
        \/ in_regions [ (p_thr (a_pl A0), 4096); (p_ctx (a_pl A0), 0x10000); (p_ri (a_pl A0), 4096);
                        (p_fs (a_pl A0), kFakeStackBytes); (p_nodes0 (a_pl A0), kDepotNodesBlock);
                        (p_frames0 (a_pl A0), kStackStoreBlockBytes); (p_pa (a_pl A0), 8 * kChunksBlockCount);
                        (p_itab (a_pl A0), 0x38e000); (p_m64k (a_pl A0), 0x10000); (p_dtls (a_pl A0), 4096);
                        (p_gvec (a_pl A0), 4096); (p_dvec (a_pl A0), 4096); (p_m11 (a_pl A0), 4096) ] a
        \/ (sh (p_fs (a_pl A0)) <= a < sh (p_fs (a_pl A0)) + kFakeStackBytes / 8)
        \/ ghost_hs_ (a_pl A0) a   (* [comment removed for export] *);
    a0_owned_not_stack : forall a, sp0 - 0x800000 <= a < 2^47 -> ~ pa_owned A0 a;
    a0_owned_not_stack_shadow : forall a, sh alloc_ceiling <= a < kHighMemBeg -> ~ pa_owned A0 a;
    a0_wfplace : wf_place AL_pasan (a_pl A0)
  }.

  (* [comment removed for export] *)
  Definition ainit_of_raw_stmt : Prop :=
    forall P k1 sp0 FULL md,
      depot_init_ok DR -> a0_raw P k1 sp0 FULL md ->
      exists A0, pa_ainv A0 FULL md /\ a0_facts sp0 A0 /\ A0 = A0_of P k1.
End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
