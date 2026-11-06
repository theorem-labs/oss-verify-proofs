(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg Hoare.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record heap_layout : Type := HL {
  hl_segs      : list Segment;        (* [comment removed for export] *)
  hl_malloc    : Z;                   (* [comment removed for export] *)
  hl_free      : Z;                   (* [comment removed for export] *)
  hl_aligned_alloc : Z;               (* [comment removed for export] *)
  hl_tp        : Z;                   (* [comment removed for export] *)
  hl_errno     : Z;                   (* [comment removed for export] *)
  hl_img_lo    : Z;                   (* [comment removed for export] *)
  hl_img_hi    : Z;
  hl_alloc_static : Z -> Prop;        (* [comment removed for export] *)
  hl_alloc_ro  : Z -> Prop;           (* [comment removed for export] *)
  hl_stack     : Z;                   (* [comment removed for export] *)
  hl_sptop     : Z;                   (* [comment removed for export] *)
  hl_k_per_malloc : Z;                (* [comment removed for export] *)
  hl_b_overhead : Z;                  (* [comment removed for export] *)
  hl_K0 : Z; hl_B0 : Z                (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Abbreviation hl_ceil L := (hl_sptop L - 8388608).
(* [comment removed for export] *)

Lemma hl_ceil_eq : forall L, hl_ceil L = hl_sptop L - 2 ^ 23.
Proof. intros L. reflexivity. Qed.

Definition credit : Type := (Z * Z)%type.   (* [comment removed for export] *)
Definition credit_ok (L : heap_layout) (cr : credit) (n : Z) : Prop :=
  hl_k_per_malloc L <= fst cr /\ n + hl_b_overhead L <= snd cr.
Definition debit (L : heap_layout) (cr : credit) (n : Z) : credit :=
  (fst cr - hl_k_per_malloc L, snd cr - (n + hl_b_overhead L)).

(* [comment removed for export] *)
Definition in_block (LB : list (Z * Z)) (a : Z) : Prop :=
  exists b, In b LB /\ fst b <= a < fst b + snd b.

(* [comment removed for export] *)
Definition client_addr (L : heap_layout) (LB : list (Z * Z)) (sp scratch : Z) (a : Z) : Prop :=
  in_block LB a
  \/ (hl_ceil L <= a < 2 ^ 64 /\ ~ (sp - scratch <= a < sp))
  \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a).

(* [comment removed for export] *)
Definition in_errno (L : heap_layout) (a : Z) : Prop := hl_errno L <= a < hl_errno L + 4.

(* [comment removed for export] *)
Definition heap_pres_core (L : heap_layout) (LB : list (Z * Z)) (sp : Z) (M M' : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (hl_stack L) a -> ~ in_errno L a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall a, sp - hl_stack L <= a < sp -> M' (Z_to_bv 64 a) <> None).   (* [comment removed for export] *)
  (* [comment removed for export] *)

Definition heap_pres (L : heap_layout) (LB : list (Z * Z)) (sp : Z) (M M' : word -> option byte) : Prop :=
  heap_pres_core L LB sp M M'
  /\ rdn (hl_segs L) M' (Z_to_bv 64 (hl_errno L)) 4 = rdn (hl_segs L) M (Z_to_bv 64 (hl_errno L)) 4.   (* [comment removed for export] *)

Definition defined (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.

Definition blocks_apart (A n : Z) (LB : list (Z * Z)) : Prop :=
  forall b, In b LB -> A + n <= fst b \/ fst b + snd b <= A.

(* [comment removed for export] *)
Definition block_range (L : heap_layout) (A n : Z) : Prop :=
  4096 <= A /\ (A + n <= hl_img_lo L \/ hl_img_hi L <= A) /\ A mod 16 = 0 /\ 0 < n /\ A + n <= hl_ceil L.

Fixpoint lb_remove (A : Z) (LB : list (Z * Z)) : list (Z * Z) :=
  match LB with
  | [] => []
  | b :: LB' => if Z.eqb (fst b) A then LB' else b :: lb_remove A LB'
  end.

(* [comment removed for export] *)
Definition callee_saved_idx : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition regs_preserved (R R' : bvmap 5 word) : Prop :=
  forall r : bv 5, In (bv_unsigned r) callee_saved_idx -> getr R' r = getr R r.

(* [comment removed for export] *)
Definition model_but_vm (m m' : Model) : Prop :=
  m' = with_vmmaps (m_vmmaps m') m.

(* [comment removed for export] *)
Section Iface.
Variable L : heap_layout.
Variable scfg : SpuriousCfg.      (* [comment removed for export] *)

Record heap_iface : Type := HI {
  (* [comment removed for export] *)
  hi_heap : list (Z * Z) -> credit -> (word -> option byte) -> VmMaps -> Prop
}.

Variable HI : heap_iface.

(* [comment removed for export] *)
Definition stack_ok (M : word -> option byte) (sp : Z) : Prop :=
  sp mod 16 = 0 /\ hl_ceil L + hl_stack L <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\
  (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= hl_stack L ->
      store_ok (hl_segs L) M (Z_to_bv 64 (sp - hl_stack L + d)) m = true).

(* [comment removed for export] *)
Lemma stack_ok_floor : forall M sp, stack_ok M sp -> 0x7fff7f800000 + hl_stack L <= sp.
Proof. intros M sp (_ & H & _ & (Hlo & _) & _). lia. Qed.

(* [comment removed for export] *)
Definition malloc_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 ->
    credit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->                      (* [comment removed for export] *)
    stack_ok M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.


(* [comment removed for export] *)
Definition aligned_alloc16_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 ->
    credit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->                      (* [comment removed for export] *)
    stack_ok M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_aligned_alloc L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition free_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (A n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    In (A, n) LB ->
    getr R 10%bv = Z_to_bv 64 A ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->                      (* [comment removed for export] *)
    stack_ok M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        heap_pres L (lb_remove A LB) (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI (lb_remove A LB) cr M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition free_null_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 10%bv = Z_to_bv 64 0 ->
    Hoare.ret_ok (getr R 1%bv) ->
    K [] ->
    (forall R', regs_preserved R R' ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M (seg_rom (hl_segs L))) model) K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition alloc_private (LB : list (Z * Z)) (a : Z) : Prop :=
  (a < hl_ceil L /\ ~ in_block LB a /\ ~ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a))
  \/ hl_alloc_ro L a.

Definition heap_frame : Prop :=
  forall LB cr M M' VM,
    hi_heap HI LB cr M VM ->
    (forall a, 0 <= a < 2 ^ 64 -> alloc_private LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    hi_heap HI LB cr M' VM.

(* [comment removed for export] *)
Definition heap_blocks_wf : Prop :=
  forall LB cr M VM, hi_heap HI LB cr M VM ->
    (forall b, In b LB -> block_range L (fst b) (snd b) /\ defined M (fst b) (snd b)
                       /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB))
    /\ NoDup (map fst LB) /\ 0 <= fst cr /\ 0 <= snd cr.

(* [comment removed for export] *)
Definition heap_perm : Prop :=
  forall LB LB' cr M VM, hi_heap HI LB cr M VM -> (forall b, In b LB <-> In b LB') -> NoDup (map fst LB') ->
    hi_heap HI LB' cr M VM.

Record heap_iface_ok : Prop := HIOK {
  hio_malloc : malloc_spec;
  hio_aligned : aligned_alloc16_spec;
  hio_free : free_spec;
  hio_free_null : free_null_spec;
  hio_frame : heap_frame;
  hio_wf : heap_blocks_wf;
  hio_perm : heap_perm
}.
End Iface.

(* [comment removed for export] *)
Definition init_vm (L : heap_layout) (lim : Z) (VM : VmMaps) : Prop :=
  exists brk0 mbase isp,
    VM = mkVmMapsFull (segments_reserved (hl_segs L)) [] [] brk0 brk0 lim mbase isp /\
    valid_brk (hl_segs L) brk0 /\ valid_mmap_base mbase /\ valid_sp isp /\ bv_unsigned isp = hl_sptop L.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma init_vm_alloc_top : forall L lim VM, init_vm L lim VM -> alloc_top VM = hl_ceil L.
Proof.
  intros L lim VM (brk0 & mbase & isp & -> & _ & _ & _ & Hsp).
  unfold alloc_top. cbn [vm_init_sp]. rewrite Hsp. rewrite stack_max_size_val. reflexivity.
Qed.
