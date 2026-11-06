(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg RefMocc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling Mem Cells Step Frame.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_AKit.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Record LibLayout := mkLibLayout {
  ll_alloc : AllocLayout;      (* [comment removed for export] *)
  ll_entry : Z;                (* [comment removed for export] *)
  ll_bss   : Z;                (* [comment removed for export] *)
  (* [comment removed for export] *)
  ll_img_ok : (word -> option byte) -> Prop;
  (* [comment removed for export] *)
  ll_img_lo : Z;
  ll_img_hi : Z;
  ll_img_intro : forall m, mem_inv (al_segs ll_alloc) m ->
                   (forall i, ll_img_lo <= i < ll_img_hi -> m (Z_to_bv 64 i) = None) -> ll_img_ok m;
  (* [comment removed for export] *)
  ll_guard : Z
}.

(* [comment removed for export] *)
Definition LIB_STACK : Z := 16384.

(* [comment removed for export] *)
Definition LIB_LIVE (N : Z) : Z := 29 * N + 16777216.
Definition LIB_NLIVE : Z := 16.

Section WithLayout.
  Context {Clg : Ceiling} (LL : LibLayout) {AI : AllocSpec (ll_alloc LL)}.   (* [comment removed for export] *)

  Let L := ll_alloc LL.
  Let segs := al_segs L.
  Let rom := seg_rom (al_segs L).

  (* [comment removed for export] *)
  Record lib_pre (R : bvmap 5 word) (m : word -> option byte) (md : Model) (A : AS)
                 (data : Z) (inp : list byte) : Prop := {
    (* [comment removed for export] *)
    lp_a0  : getr R 10 = Z_to_bv 64 data;
    lp_a1  : getr R 11 = Z_to_bv 64 (Z.of_nat (length inp));
    lp_tp  : getr R 4 = al_tp L;
    lp_ra4 : bv_unsigned (getr R 1) mod 4 = 0;
    lp_sp16 : bv_unsigned (getr R 2) mod 16 = 0;
    lp_sp_lo : alloc_ceiling + 65536 + LIB_STACK <= bv_unsigned (getr R 2);
    lp_sp_hi : bv_unsigned (getr R 2) + 64 <= 2^47;       (* [comment removed for export] *)
    (* [comment removed for export] *)
    lp_mi  : mem_inv segs m;
    lp_stk : stk segs m (bv_unsigned (getr R 2) - LIB_STACK) (bv_unsigned (getr R 2));
    lp_errno : exists e, rw_cells segs m (al_errno L) [C4 e];
    lp_bss : exists v1 v2, rw_cells segs m (ll_bss LL) [C8 v1; C8 v2];
    lp_img : ll_img_ok LL m;
    lp_guard : exists g : word, rw_cells segs m (ll_guard LL) [C8 g];
    (* [comment removed for export] *)
    lp_size : Z.of_nat (length inp) < 2^26;
    lp_inp : length inp <> 0%nat -> a_live A data = Some (Z.of_nat (length inp)) /\ bytes_at segs m data inp;
    (* [comment removed for export] *)
    lp_ainv : ainv A m md;
    (* [comment removed for export] *)
    lp_budget : a_livebytes A + LIB_LIVE (Z.of_nat (length inp)) <= LIVE_MAX /\ a_nlive A + LIB_NLIVE <= NLIVE_MAX
  }.

  (* [comment removed for export] *)
  Record lib_post (R : bvmap 5 word) (m : word -> option byte) (md : Model) (A : AS)
                  (R' : bvmap 5 word) (m' : word -> option byte) (md' : Model) (A' : AS) : Prop := {
    (* [comment removed for export] *)
    lq_cs : keeps_cs R R';
    lq_a0 : getr R' 10 = Z_to_bv 64 0;
    (* [comment removed for export] *)
    lq_mdf : md_frame md md';
    lq_ainv : ainv A' m' md';
    (* [comment removed for export] *)
    lq_budget : a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A;
    (* [comment removed for export] *)
    lq_live : forall p n, a_live A p = Some n -> a_live A' p = Some n;
    lq_live_bytes : forall p n i, a_live A p = Some n -> 0 <= i < n -> m' (Z_to_bv 64 (p + i)) = m (Z_to_bv 64 (p + i));
    (* [comment removed for export] *)
    lq_mi  : mem_inv segs m';
    lq_stk : stk segs m' (bv_unsigned (getr R 2) - LIB_STACK) (bv_unsigned (getr R 2));
    lq_errno : exists e, rw_cells segs m' (al_errno L) [C4 e];
    lq_bss : exists v1 v2, rw_cells segs m' (ll_bss LL) [C8 v1; C8 v2];
    lq_img : ll_img_ok LL m';
    lq_guard : exists g : word, rw_cells segs m' (ll_guard LL) [C8 g];
    (* [comment removed for export] *)
    lq_cframe : cframe L (owned A) (owned A') (bv_unsigned (getr R 2)) LIB_STACK
                       (fun a => ll_bss LL <= a < ll_bss LL + 16) nowhere m m'
  }.

  (* [comment removed for export] *)
  Definition lib_call_ok : Prop :=
    forall (R : bvmap 5 word) (m : word -> option byte) (md : Model) (A : AS)
           (data : Z) (inp : list byte) (T : TSet),
      lib_pre R m md A data inp ->
      (forall R' m' md' A',
          lib_post R m md A R' m' md' A' ->
          realizes segs (mkCfg (mkst R' (getr R 1) m' rom) md') T) ->
      realizes segs (mkCfg (mkst R (Z_to_bv 64 (ll_entry LL)) m rom) md) T.

End WithLayout.

Arguments lib_pre {Clg} LL {AI}.
Arguments lib_post {Clg} LL {AI}.
Arguments lib_call_ok {Clg} LL {AI}.
