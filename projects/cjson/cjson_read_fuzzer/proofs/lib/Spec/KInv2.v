(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim STree Malloc MallocCtrl Prog KInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition went (b n : Z) : word * word := (Z_to_bv 64 b, Z_to_bv 64 n).
Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).
Definition ehi (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).

(* [comment removed for export] *)
Definition wcov (maps : list (word * word)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> exists e, In e maps /\ elo e <= x < ehi e.

(* [comment removed for export] *)
Definition edisj (e1 e2 : word * word) : Prop := ehi e1 <= elo e2 \/ ehi e2 <= elo e1.
Inductive pwdisj : list (word * word) -> Prop :=
| pwdisj_nil : pwdisj []
| pwdisj_cons e l : (forall e', In e' l -> edisj e e') -> pwdisj l -> pwdisj (e :: l).
Definition vmwf (maps : list (word * word)) : Prop :=
  (forall e, In e maps -> elo e < ehi e <= 2^64) /\ pwdisj maps.

(* [comment removed for export] *)
Definition brk_disj (L : mled) (b n : Z) : Prop :=
  forall b0 l0, ld_brkreg L = Some (b0, l0) -> b + n <= b0 + PGSZ \/ b0 + l0 <= b.

(* [comment removed for export] *)
Definition resv_disj (h : VmMaps) (b n : Z) : Prop :=
  forall e, In e (vm_reserved h) -> b + n <= elo e \/ ehi e <= b.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition phase_inv (ph : brk_phase) (L : mled) (pbrk : Z) (mo : Model) : Prop :=
  let h := m_vmmaps mo in
  match ph with
  | BPUntried => vm_brk h = vm_start_brk h /\ ld_brkreg L = None
  | BPQueried cur => cur = bv_unsigned (vm_start_brk h)
      /\ bv_unsigned (vm_brk h) = cur /\ pbrk = cur /\ ld_brkreg L = None
  | BPGuard cur => cur = bv_unsigned (vm_start_brk h)
      /\ bv_unsigned (vm_brk h) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
      /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
      /\ In (went cur (2 * PGSZ)) (vm_maps h)
      /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
  | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk h) = b + l /\ pbrk = b + l
  | BPDead => True
  end.

(* [comment removed for export] *)
Definition brk_piece (L : mled) (e : word * word) : Prop :=
  match ld_brkreg L with
  | Some (b, l) => e = went b (2 * PGSZ) \/ exists j, 1 <= j /\ (j + 1) * PGSZ <= l /\ e = went (b + j * PGSZ) PGSZ
  | None => match ld_brk L with BPGuard cur => e = went cur (2 * PGSZ) | _ => False end
  end.

(* [comment removed for export] *)
Definition drv_limit : Z := 2^31.

(* [comment removed for export] *)
Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_lazy : m_vm_lazy mo = [];
  kl_mat : m_vm_materialized mo = [];
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  kl_resv : ld_resv L = map wwZ (vm_reserved (m_vmmaps mo));
  kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo));
  kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_ceiling;
  kl_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ resv_disj (m_vmmaps mo) b (mmap_len l);
  kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
      /\ b = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  (* [comment removed for export] *)
  kl_na : forall e, In e (vm_noaccess (m_vmmaps mo)) ->
      elo e < ehi e /\
      ((exists b l k, In (b, l, k) (ld_metas L) /\ b <= elo e /\ ehi e <= b + mmap_len l)
       \/ (exists b l, ld_brkreg L = Some (b, l) /\ b <= elo e /\ ehi e <= b + PGSZ
                       /\ In (went b (2 * PGSZ)) (vm_maps (m_vmmaps mo))));
  kl_lim : drv_limit <= vm_limit (m_vmmaps mo);
  (* [comment removed for export] *)
  kl_cov : forall e, In e (vm_maps (m_vmmaps mo)) ->
      (exists b l, In (b, l) (ld_groups L) /\ e = went b (mmap_len l))
      \/ (exists b l k, In (b, l, k) (ld_metas L) /\ e = went b (mmap_len l))
      \/ brk_piece L e;
  kl_phase : phase_inv (ld_brk L) L pbrk mo;
  (* [comment removed for export] *)
  kl_top : alloc_top (m_vmmaps mo) = alloc_ceiling }.

(* [comment removed for export] *)
Definition ev_step_post (L : mled) (e : ev) (s0 : PState) (mo0 : Model)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0 /\ vm_only mo0 mo.

(* [comment removed for export] *)


End CeilWrap.
