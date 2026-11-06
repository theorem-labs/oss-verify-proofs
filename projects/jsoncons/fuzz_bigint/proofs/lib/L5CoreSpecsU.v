(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5CSU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition TP : Z := 462648.
Definition HEAP_STACK : Z := 8224.      (* [comment removed for export] *)

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
Record layout (L : heap_layout) : Prop := LAY {
  ly_segs : hl_segs L = RSEGS;
  ly_malloc : hl_malloc L = 0x4c440;
  ly_free : hl_free L = 0x4c300;
  ly_aligned : hl_aligned_alloc L = 0x4c444;
  ly_tp : hl_tp L = TP;
  ly_errno : hl_errno L = 0x70e94;
  ly_img_lo : hl_img_lo L = 0x10000;
  ly_img_hi : hl_img_hi L = 0x92000;
  ly_stack : hl_stack L = HEAP_STACK;
  ly_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a;   (* [comment removed for export] *)
  ly_static : forall a, hl_alloc_static L a -> 0x91238 <= a < 0x915e0 }.

(* [comment removed for export] *)
Definition model_ok (model : Model) : Prop :=
  m_halted model = None /\ m_vm_lazy model = [] /\ m_vm_materialized model = [].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPNEW : Z := 0x5abac.
Definition OPNEW_SCR : Z := 16 + HEAP_STACK.

Definition opnew_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> credit_ok L cr n ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A -> regs_preserved R R' ->
        L5C.fresh_block L LB M' A n ->
        L5C.hpres L LB sp OPNEW_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI ((A, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R OPNEW M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPDEL : Z := 0x3f720.
Definition OPDEL_SIZED : Z := 0x3f724.
Definition OPDEL_SCR : Z := HEAP_STACK.

Definition opdel_spec_at (pc : Z) (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (A n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    In (A, n) LB -> getr R 10%bv = Z_to_bv 64 A ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp OPDEL_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5C.hpres L (lb_remove A LB) sp OPDEL_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI (lb_remove A LB) cr M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.
Definition opdel_spec := opdel_spec_at OPDEL.
Definition opdel_sized_spec := opdel_spec_at OPDEL_SIZED.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ROUNDUP : Z := 0x21980.
Definition ROUNDUP_SCR : Z := 48.
Definition round_up (i : Z) : Z := 8 * (i / 8) + 8.

Definition roundup_post (R R' : bvmap 5 word) (M M' : word -> option byte) (sp i : Z) : Prop :=
  getr R' 10%bv = Z_to_bv 64 (round_up i) /\ regs_preserved R R' /\ L5.frame_but [(sp - ROUNDUP_SCR, ROUNDUP_SCR)] M M' /\ mem_grows M M'.

Definition roundup_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (i sp r : Z),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 10%bv = Z_to_bv 64 i -> 0 <= i <= 2 ^ 62 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 16 = 0 -> 2 ^ 20 <= sp - ROUNDUP_SCR -> sp <= 2 ^ 47 ->
    L5.writable RSEGS M (sp - ROUNDUP_SCR) ROUNDUP_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        roundup_post R R' M M' sp i -> srealizes RSEGS SCFG (cfg R' r M' model) K) ->
    srealizes RSEGS SCFG (cfg R ROUNDUP M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARESERVE : Z := 0x21858.
Definition ARESERVE_SCR : Z := 64 + OPNEW_SCR.

Definition areserve_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 n -> 1 <= n <= 2 ^ 23 -> credit_ok L cr (8 * round_up n) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp ARESERVE_SCR ->
    o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    L5.u64_at RSEGS M (o + 8) 0 -> L5.u64_at RSEGS M (o + 24) 0 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        regs_preserved R R' ->
        L5C.fresh_block L LB M' A (8 * round_up n) ->
        L5.u64_at RSEGS M' (o + 16) (round_up n) /\ L5.u64_at RSEGS M' (o + 24) A ->
        L5C.hpres L LB sp ARESERVE_SCR [(o + 16, 16)] M M' ->
        model_but_vm model model' -> hi_heap HI ((A, 8 * round_up n) :: LB) (debit L cr (8 * round_up n)) M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R ARESERVE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RESERVE : Z := 0x21644.
Definition RESERVE_SCR : Z := 48 + ARESERVE_SCR.

(* [comment removed for export] *)
Inductive growth : Type := Same | Grown (A : Z) (cap : Z).

Definition reserve_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp n : Z) (b : L5.bigobj) (g : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  match g with
  | Same => (L5.bo_dyn b = true \/ n <= 2) /\ LB' = LB /\ cr' = cr
            /\ L5.big_at RSEGS M' o b
            /\ L5C.hpres L LB sp RESERVE_SCR [] M M'
  | Grown A cap => L5.bo_dyn b = false /\ 3 <= n /\ cap = round_up n /\ LB' = (A, 8 * cap) :: LB /\ cr' = debit L cr (8 * cap)
            /\ L5C.fresh_block L LB M' A (8 * cap)
            /\ (exists v0 v1, L5.bo_st b = L5.BInl v0 v1 /\ L5.u64_at RSEGS M' A v0 /\ L5.u64_at RSEGS M' (A + 8) v1)
            /\ L5.big_at RSEGS M' o (L5.BO (Z.lor (L5.bo_fb b) 1) (L5.bo_len b) (L5.BDyn cap A))
            /\ L5C.hpres L LB sp RESERVE_SCR [(o, 32)] M M'
  end.

Definition reserve_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o n sp r : Z) (b : L5.bigobj),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 n -> 0 <= n <= 2 ^ 23 ->
    (L5.bo_dyn b = true -> n <= L5.bo_cap b) ->                    (* [comment removed for export] *)
    (L5.bo_dyn b = false -> 3 <= n -> credit_ok L cr (8 * round_up n)) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp RESERVE_SCR ->
    L5.big_at RSEGS M o b -> o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        reserve_post L LB cr M M' R R' o sp n b g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R RESERVE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RESIZE : Z := 0x214e4.
Definition RESIZE_SCR : Z := 64 + RESERVE_SCR.

(* [comment removed for export] *)
Definition resize_limbs (ws : list Z) (n : nat) : list Z := firstn n ws ++ repeat 0 (n - length ws).

Definition resize_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp : Z) (n : nat) (b : L5.bigobj) (ws : list Z) (g : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  match g with
  | Same => (L5.bo_dyn b = true \/ (n <= 2)%nat) /\ LB' = LB /\ cr' = cr
            /\ (exists st', L5.big_at RSEGS M' o (L5.BO (L5.bo_fb b) n st') /\ L5C.obj_limbs RSEGS M' (L5.BO (L5.bo_fb b) n st') (resize_limbs ws n)
                           /\ match L5.bo_st b, st' with
                              | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
                              | L5.BInl _ _, L5.BInl _ _ => True
                              | _, _ => False end)
            /\ L5C.hpres L LB sp RESIZE_SCR [(o, 32); (L5.bo_data o b + 8 * Z.of_nat (L5.bo_len b), 8 * Z.max 0 (Z.of_nat n - Z.of_nat (L5.bo_len b)))] M M'
  | Grown A cap => L5.bo_dyn b = false /\ (3 <= n)%nat /\ cap = round_up (Z.of_nat n) /\ LB' = (A, 8 * cap) :: LB /\ cr' = debit L cr (8 * cap)
            /\ L5C.fresh_block L LB M' A (8 * cap)
            /\ L5.big_at RSEGS M' o (L5.BO (Z.lor (L5.bo_fb b) 1) n (L5.BDyn cap A))
            /\ L5C.obj_limbs RSEGS M' (L5.BO (Z.lor (L5.bo_fb b) 1) n (L5.BDyn cap A)) (resize_limbs ws n)
            /\ L5C.hpres L LB sp RESIZE_SCR [(o, 32)] M M'
  end.

Definition resize_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o sp r : Z) (n : nat) (b : L5.bigobj) (ws : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 (Z.of_nat n) -> Z.of_nat n <= 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat n <= L5.bo_cap b) ->
    ((3 <= n)%nat -> L5.bo_dyn b = false -> credit_ok L cr (8 * round_up (Z.of_nat n))) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp RESIZE_SCR ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws ->
    o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        resize_post L LB cr M M' R R' o sp n b ws g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R RESIZE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASSIGN : Z := 0x21428.
Definition ASSIGN_SCR : Z := 48 + RESIZE_SCR.

(* [comment removed for export] *)
Definition assign_fb (fb fb' : Z) (leny : nat) (grown : bool) : Z :=
  let f0 := if grown then Z.lor fb 1 else fb in
  if Nat.eqb leny 0 then f0 else Z.lor (Z.land f0 253) (Z.land fb' 2).

Definition assign_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o o' sp : Z) (b b' : L5.bigobj) (ws' : list Z) (g : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o /\
  let n := L5.bo_len b' in
  match g with
  | Same => (L5.bo_dyn b = true \/ (n <= 2)%nat) /\ LB' = LB /\ cr' = cr
            /\ (exists st', L5.big_at RSEGS M' o (L5.BO (assign_fb (L5.bo_fb b) (L5.bo_fb b') n false) n st')
                           /\ L5C.obj_limbs RSEGS M' (L5.BO (assign_fb (L5.bo_fb b) (L5.bo_fb b') n false) n st') ws'
                           /\ match L5.bo_st b, st' with
                              | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
                              | L5.BInl _ _, L5.BInl _ _ => True
                              | _, _ => False end)
            /\ L5C.hpres L LB sp ASSIGN_SCR [(o, 32); (L5.bo_data o b, 8 * Z.max (Z.of_nat n) (Z.of_nat (L5.bo_len b)))] M M'
  | Grown A cap => L5.bo_dyn b = false /\ (3 <= n)%nat /\ cap = round_up (Z.of_nat n) /\ LB' = (A, 8 * cap) :: LB /\ cr' = debit L cr (8 * cap)
            /\ L5C.fresh_block L LB M' A (8 * cap)
            /\ L5.big_at RSEGS M' o (L5.BO (assign_fb (L5.bo_fb b) (L5.bo_fb b') n true) n (L5.BDyn cap A))
            /\ L5C.obj_limbs RSEGS M' (L5.BO (assign_fb (L5.bo_fb b) (L5.bo_fb b') n true) n (L5.BDyn cap A)) ws'
            /\ L5C.hpres L LB sp ASSIGN_SCR [(o, 32)] M M'
  end.

Definition assign_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o o' sp r : Z) (b b' : L5.bigobj) (ws' : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 o' -> Z.of_nat (L5.bo_len b') <= 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b') <= L5.bo_cap b) ->
    ((3 <= L5.bo_len b')%nat -> L5.bo_dyn b = false -> credit_ok L cr (8 * round_up (Z.of_nat (L5.bo_len b')))) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp ASSIGN_SCR ->
    L5.big_at RSEGS M o b -> o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    L5.big_at RSEGS M o' b' -> L5C.obj_limbs RSEGS M b' ws' -> o' mod 8 = 0 -> sp <= o' -> o' + 32 <= hl_sptop L ->
    (forall cap q, L5.bo_st b' = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (o + 32 <= o' \/ o' + 32 <= o) ->
    (forall c q c' q', L5.bo_st b = L5.BDyn c q -> L5.bo_st b' = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->   (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        assign_post L LB cr M M' R R' o o' sp b b' ws' g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R ASSIGN M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition COPY : Z := 0x222d0.
Definition COPYA : Z := 0x23208.
Definition ACOPY : Z := 0x2233c.
Definition COPY_SCR : Z := 64 + OPNEW_SCR.    (* [comment removed for export] *)

Definition copy_fb (fbo fb' : Z) (dyn : bool) : Z :=
  Z.lor (Z.lor (Z.land fbo 252) (if dyn then 1 else 0)) (Z.land fb' 2).

Definition copy_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o o' sp fbo : Z) (b' : L5.bigobj) (ws' : list Z) (g : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  match g with
  | Same => L5.bo_dyn b' = false /\ LB' = LB /\ cr' = cr
            /\ L5.big_at RSEGS M' o (L5.BO (copy_fb fbo (L5.bo_fb b') false) (L5.bo_len b') (L5.bo_st b'))
            /\ L5.frame_but [(o, 32)] M M' /\ mem_grows M M'
  | Grown A cap => L5.bo_dyn b' = true /\ cap = L5.bo_cap b' /\ LB' = (A, 8 * cap) :: LB /\ cr' = debit L cr (8 * cap)
            /\ L5C.fresh_block L LB M' A (8 * cap)
            /\ L5.big_at RSEGS M' o (L5.BO (copy_fb fbo (L5.bo_fb b') true) (L5.bo_len b') (L5.BDyn cap A))
            /\ L5C.obj_limbs RSEGS M' (L5.BO (copy_fb fbo (L5.bo_fb b') true) (L5.bo_len b') (L5.BDyn cap A)) ws'
            /\ L5C.hpres L LB sp COPY_SCR [(o, 32)] M M'
  end.

Definition copy_spec_at (pc : Z) (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o o' sp r fbo : Z) (b' : L5.bigobj) (ws' : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 o' ->
    (L5.bo_dyn b' = true -> 8 * L5.bo_cap b' <= 2 ^ 27 /\ credit_ok L cr (8 * L5.bo_cap b')) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp COPY_SCR ->
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 -> o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    L5.big_at RSEGS M o' b' -> L5C.obj_limbs RSEGS M b' ws' -> o' mod 8 = 0 -> sp <= o' -> o' + 32 <= hl_sptop L ->
    (forall cap q, L5.bo_st b' = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (o + 32 <= o' \/ o' + 32 <= o) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        copy_post L LB cr M M' R R' o o' sp fbo b' ws' g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.
Definition copy_spec := copy_spec_at COPY.
Definition copya_spec := copy_spec_at COPYA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRINIT : Z := 0x20a84.
Definition STRINIT_SCR : Z := 48 + OPNEW_SCR.
Definition str_cap (n : Z) : Z := if Z.eqb (Z.lor n 7) 23 then 26 else Z.lor n 7 + 1.

Definition strinit_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp : Z) (s : list Z) (g : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  match g with
  | Same => (length s <= 22)%nat /\ LB' = LB /\ cr' = cr /\ L5.lstr_short RSEGS M' o s
            /\ L5.frame_but [(sp - STRINIT_SCR, STRINIT_SCR); (o, 24)] M M' /\ mem_grows M M'
  | Grown p cap => (23 <= length s)%nat /\ cap = str_cap (Z.of_nat (length s)) /\ LB' = (p, cap) :: LB /\ cr' = debit L cr cap
            /\ L5C.fresh_block L LB M' p cap
            /\ L5.lstr_long RSEGS M' o s (cap + 1) p
            /\ L5C.hpres L LB sp STRINIT_SCR [(o, 24)] M M'
  end.

Definition strinit_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o src sp r : Z) (s : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 src -> getr R 12%bv = Z_to_bv 64 (Z.of_nat (length s)) ->
    Z.of_nat (length s) < 2 ^ 26 -> Forall (fun c => 0 <= c < 256) s ->
    ((23 <= length s)%nat -> credit_ok L cr (str_cap (Z.of_nat (length s)))) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp STRINIT_SCR ->
    o mod 8 = 0 -> sp <= o -> o + 24 <= hl_sptop L -> L5.writable RSEGS M o 24 ->
    L5.bytes_at RSEGS M src s -> L5.defined M src (Z.of_nat (length s)) ->
    (* [comment removed for export] *)
    (length s = 0%nat \/ (exists A m, In (A, m) LB /\ A <= src /\ src + Z.of_nat (length s) <= A + m)
                     \/ (sp <= src /\ src + Z.of_nat (length s) <= 2 ^ 47)) ->
    (o + 24 <= src \/ src + Z.of_nat (length s) <= o) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        strinit_post L LB cr M M' R R' o sp s g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R STRINIT M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MUL10 : Z := 0x210e4.
Definition MUL10_SCR : Z := 96 + RESIZE_SCR.
Definition ADDD : Z := 0x21250.
Definition ADDD_SCR : Z := 112 + RESIZE_SCR.

(* [comment removed for export] *)
Definition reduced (ws : list Z) : Prop := ws = [] \/ nth (length ws - 1) ws 0 <> 0.

Definition arith_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp SCR : Z) (b : L5.bigobj) (V' : Z) (g : growth) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 o /\
  exists (ws' : list Z) (st' : L5.bstore),
    L5.limbs_val ws' = V' /\ reduced ws' /\ (Z.of_nat (length ws') <= Z.of_nat (L5.bo_len b) + 1) /\
    let b1 := L5.BO (match g with Same => L5.bo_fb b | Grown _ _ => Z.lor (L5.bo_fb b) 1 end) (length ws') st' in
    L5.big_at RSEGS M' o b1 /\ L5C.obj_limbs RSEGS M' b1 ws' /\
    match g with
    | Same => (L5.bo_dyn b = true \/ (L5.bo_len b <= 1)%nat) /\ LB' = LB /\ cr' = cr
              /\ match L5.bo_st b, st' with
                 | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q
                 | L5.BInl _ _, L5.BInl _ _ => True
                 | _, _ => False end
              /\ L5C.hpres L LB sp SCR [(o, 32); (L5.bo_data o b, 8 * (Z.of_nat (L5.bo_len b) + 1))] M M'
    | Grown A cap => L5.bo_dyn b = false /\ L5.bo_len b = 2%nat /\ cap = 8 /\ st' = L5.BDyn 8 A /\ LB' = (A, 64) :: LB /\ cr' = debit L cr 64
              /\ L5C.fresh_block L LB M' A 64
              /\ L5C.hpres L LB sp SCR [(o, 32)] M M'
    end.

Definition mul10_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o sp r : Z) (b : L5.bigobj) (ws : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 10 -> Z.of_nat (L5.bo_len b) < 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b) + 1 <= L5.bo_cap b) ->
    (L5.bo_dyn b = false -> L5.bo_len b = 2%nat -> credit_ok L cr 64) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp MUL10_SCR ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> L5.bo_neg b = false ->
    o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        arith_post L LB cr M M' R R' o sp MUL10_SCR b (10 * L5.limbs_val ws) g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R MUL10 M model) K.

Definition addd_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o d sp r : Z) (b : L5.bigobj) (ws : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 d -> 0 <= d <= 9 -> Z.of_nat (L5.bo_len b) < 2 ^ 23 ->
    (L5.bo_dyn b = true -> Z.of_nat (L5.bo_len b) + 1 <= L5.bo_cap b) ->
    (L5.bo_dyn b = false -> L5.bo_len b = 2%nat -> credit_ok L cr 64) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp ADDD_SCR ->
    L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> L5.bo_neg b = false ->
    o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        arith_post L LB cr M M' R R' o sp ADDD_SCR b (L5.limbs_val ws + d) g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R ADDD M model) K.
End SCFG_1.


End L5CSU.
