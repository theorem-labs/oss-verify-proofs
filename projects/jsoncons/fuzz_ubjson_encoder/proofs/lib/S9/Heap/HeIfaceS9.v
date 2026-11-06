(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk ShapeAlg SpinAlg Hoare HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition NREQ : Z := 2 ^ 35 + 2 ^ 32 - 2 ^ 16.
Definition NREQA : Z := 2 ^ 30 - 2 ^ 16.

Definition cszR (n : Z) : Z := Z.max (2 ^ 20) ((n + 20 + 4095) / 4096 * 4096).

Definition credit_okR (cr : credit) (n : Z) : Prop := 1 <= fst cr /\ cszR n <= snd cr.
Definition debitR (cr : credit) (n : Z) : credit := (fst cr - 1, snd cr - cszR n).
Definition refundR (cr : credit) (n : Z) : credit := (fst cr + 1, snd cr + cszR n).

Lemma cszR_small n : 0 <= n <= 2 ^ 20 - 20 -> cszR n = 2 ^ 20.
Proof.
  intros Hn. unfold cszR. change (2 ^ 20) with 1048576 in *. apply Z.max_l.
  assert ((n + 20 + 4095) / 4096 < 257) by (apply Z.div_lt_upper_bound; lia).
  change 1048576 with (256 * 4096). apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Lemma cszR_ge n : 2 ^ 20 <= cszR n.
Proof. unfold cszR. apply Z.le_max_l. Qed.

Lemma refund_debit cr n : refundR (debitR cr n) n = cr.
Proof. unfold refundR, debitR. cbn. destruct cr as [k b]. cbn. f_equal; lia. Qed.

Definition fits (lim n : Z) : Prop := n < 131052 \/ (n + 20 + 4095) / 4096 * 4096 <= lim.

Lemma fits_small lim n : n < 131052 -> fits lim n.
Proof. intros H. left. exact H. Qed.
Lemma fits_le lim n : fits lim n -> 131072 <= lim -> n + 20 <= lim.
Proof. intros [H|H] Hl; [lia| Z.div_mod_to_equations; lia]. Qed.
Lemma fits_mono lim lim' n : fits lim n -> lim <= lim' -> fits lim' n.
Proof. intros [H|H] Hl; [left; exact H| right; lia]. Qed.
Lemma fits_cszR lim n : fits lim n -> 2 ^ 20 <= lim -> 0 <= n -> cszR n <= lim.
Proof.
  intros [H|H] Hl Hn; unfold cszR; apply Z.max_lub; try exact Hl; try exact H.
  change (2 ^ 20) with 1048576 in Hl. assert ((n + 20 + 4095) / 4096 <= 33) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

Lemma fits_pow2 k j : 17 <= k -> 0 <= j -> fits (2 ^ j) (2 ^ k) -> k < j.
Proof.
  intros Hk Hj [H|H].
  - exfalso. assert (2 ^ 17 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 17) with 131072 in *. lia.
  - destruct (Z.lt_ge_cases k j) as [L|G]; [exact L| exfalso].
    assert (2 ^ j <= 2 ^ k) by (apply Z.pow_le_mono_r; lia).
    generalize dependent (2 ^ k). generalize dependent (2 ^ j). intros a b H Hab. Z.div_mod_to_equations. lia.
Qed.

Section IfaceR.
Variable L : heap_layout.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.
Variable HI : heap_iface.

Definition mallocR_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NREQ ->
    credit_okR cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition alignedR_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= NREQA ->
    credit_okR cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_aligned_alloc L)) M (seg_rom (hl_segs L))) model) K.

Definition freeR_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (A n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    In (A, n) LB ->
    getr R 10%bv = Z_to_bv 64 A ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        heap_pres L (lb_remove A LB) (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI (lb_remove A LB) (refundR cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

Record heap_ifaceR_ok : Prop := HIROK {
  hir_malloc : mallocR_spec;
  hir_aligned : alignedR_spec;
  hir_free : freeR_spec;
  hir_free_null : free_null_spec L scfg;
  hir_frame : heap_frame L HI;
  hir_wf : heap_blocks_wf L HI;
  hir_perm : heap_perm HI
}.
End IfaceR.

Section IfaceE.
Variable L : heap_layout.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.
Variable HI : heap_iface.
Variable lim : Z.

Definition credit_okE (cr : credit) (n : Z) : Prop := 1 <= fst cr /\ (bm_on = true \/ cszR n <= snd cr).
Definition debitE (cr : credit) (n : Z) : credit := (fst cr - 1, Z.max 0 (snd cr - cszR n)).

Definition mallocE_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NREQ ->
    credit_okE cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitE cr n) M' (m_vmmaps model') ->
        fits lim n ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition alignedE_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= NREQA ->
    credit_okE cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitE cr n) M' (m_vmmaps model') ->
        fits lim n ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_aligned_alloc L)) M (seg_rom (hl_segs L))) model) K.

Definition heap_fit : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (M : word -> option byte) (VM : VmMaps) (A n : Z),
    hi_heap HI LB cr M VM -> In (A, n) LB -> fits lim n.
Definition heap_limit : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (M : word -> option byte) (VM : VmMaps),
    hi_heap HI LB cr M VM -> vm_limit VM = lim.

Record heap_ifaceE_ok : Prop := HIEOK {
  hie_malloc : mallocE_spec;
  hie_aligned : alignedE_spec;
  hie_free : freeR_spec L scfg HI;
  hie_free_null : free_null_spec L scfg;
  hie_frame : heap_frame L HI;
  hie_wf : heap_blocks_wf L HI;
  hie_perm : heap_perm HI;
  hie_fit : heap_fit;
  hie_limit : heap_limit
}.

Definition mallocF_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NREQ ->
    credit_okR cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debitR cr n) M' (m_vmmaps model') ->
        fits lim n ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition mallocS_spec : Prop :=
  bm_on = true ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NREQ ->
    1 <= fst cr ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (fst cr - 1, snd cr) M' (m_vmmaps model') ->
        fits lim n ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.

Definition freeS_spec : Prop :=
  bm_on = true ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (A n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    In (A, n) LB ->
    getr R 10%bv = Z_to_bv 64 A ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->
    stack_ok L M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        heap_pres L (lb_remove A LB) (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI (lb_remove A LB) (fst cr + 1, snd cr) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

Record heap_ifaceS_ok : Prop := HISOK {
  his_R : heap_ifaceR_ok L scfg HI;
  his_mallocF : mallocF_spec;
  his_mallocS : mallocS_spec;
  his_freeS : freeS_spec;
  his_fit : heap_fit;
  his_limit : heap_limit
}.
End IfaceE.

