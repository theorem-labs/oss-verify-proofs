(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the vDSO/vvar pair in the reserved ledger: kl_resv_top's above-the-brk case, kl_metas_resv and kl_vdso; kl_resv as a prefix of the model's reserved ledger, with kl_resv_in). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad MSafe STree Malloc RawAlloc KInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition went (b n : Z) : word * word := (wz b, wz n).
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
Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  (* LPS 727298f3: the ledger's reserved list is a prefix of the model's reserved ledger, whose
     tail is the launch's vDSO/vvar pair ([State.init_reserved] = reserved ++ vdso_reserved ..) *)
  kl_resv : exists t, map wwZ (vm_reserved (m_vmmaps mo)) = ld_resv L ++ t;
  (* LPS 727298f3: [init_model]'s reserved ledger is [reserved ++ vdso_reserved ..]
     (State.v [init_reserved]), and the vDSO/vvar pair sits under the mmap base, far above
     the brk start; so an entry is below the brk start OR four pages above it. *)
  kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) ->
      ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo))
      \/ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= elo e;
  kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_ceiling;
  kl_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  kl_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end;
  (* [comment removed for export] *)
  kl_groups_resv : forall b l, In (b, l) (ld_groups L) ->
      forall e, In e (vm_reserved (m_vmmaps mo)) -> b + mmap_len l <= elo e \/ ehi e <= b;
  kl_noacc : forall e, In e (vm_noaccess (m_vmmaps mo)) ->
      (exists b l k, In (b, l, k) (ld_metas L) /\ b <= elo e /\ ehi e <= b + mmap_len l)
      \/ (exists b l e0, ld_brkreg L = Some (b, l) /\ b <= elo e /\ ehi e <= b + PGSZ
                         /\ In e0 (vm_maps (m_vmmaps mo)) /\ elo e0 <= b /\ b + 2 * PGSZ <= ehi e0);
  (* [comment removed for export] *)
  kl_mat : m_vm_materialized mo = [];
  (* [comment removed for export] *)
  kl_pages : forall e, In e (vm_maps (m_vmmaps mo)) -> elo e mod PGSZ = 0 /\ ehi e mod PGSZ = 0;
  (* LPS 727298f3: [check_mprotect] declines a range that meets the vDSO/vvar pair, so a
     meta page must miss it.  Two halves, as in cjson/cjson_read_fuzzer's Spec/KInv2.v:
     a meta block misses the reserved ledger (the grant's own
     [region_free (vm_reserved ++ vm_maps)] check, as [kl_groups_resv] for a group), and the
     pair is part of that ledger ([State.init_reserved]; no node changes it,
     [Lib/Nodes.nstep_vdso]). *)
  kl_metas_resv : forall b l k, In (b, l, k) (ld_metas L) ->
      forall e, In e (vm_reserved (m_vmmaps mo)) -> b + mmap_len l <= elo e \/ ehi e <= b;
  kl_vdso : forall e, In e (vdso_of mo) -> In e (vm_reserved (m_vmmaps mo)) }.

(* every entry of the ledger's reserved list is an entry of the model's reserved ledger *)
Lemma kl_resv_in : forall L pbrk mo x, KL L pbrk mo -> In x (ld_resv L) -> In x (map wwZ (vm_reserved (m_vmmaps mo))).
Proof.
  intros L pbrk mo x HK Hx. destruct (kl_resv _ _ _ HK) as [t Et]. rewrite Et. apply in_or_app. left. exact Hx.
Qed.

(* [comment removed for export] *)
Definition frame_ok (G : PState -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> vm_only mo mo' -> G s mo -> G s' mo'.

Lemma vm_only_refl : forall mo, vm_only mo mo.
Proof. intros mo. unfold vm_only. repeat split; reflexivity. Qed.
Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof. intros a b c (?&?&?&?&?) (?&?&?&?&?). unfold vm_only. repeat split; congruence. Qed.

(* [comment removed for export] *)
Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.

(* [comment removed for export] *)
End RC__1.
