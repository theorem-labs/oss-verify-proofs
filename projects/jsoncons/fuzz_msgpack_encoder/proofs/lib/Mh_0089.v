(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.
Module HeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition SB : Z := 0x7fff8000.                       (* [comment removed for export] *)
Definition S (a : Z) : Z := a / 8 + SB.                (* [comment removed for export] *)
Definition BIGSHADOW_LO : Z := 0x7fff7000.             (* [comment removed for export] *)
Definition BIGSHADOW_HI : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition app_mem (a n : Z) : Prop := 0 <= a /\ (a + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= a) /\ a + n <= 2 ^ 47.

(* [comment removed for export] *)
Record asan_layout : Type := AL {
  hl_segs      : list Segment;        (* [comment removed for export] *)
  hl_malloc    : Z;                   (* [comment removed for export] *)
  hl_free      : Z;                   (* [comment removed for export] *)
  hl_aligned_alloc : Z;               (* [comment removed for export] *)
  hl_stack_malloc : Z -> Z;           (* [comment removed for export] *)
  hl_handle_no_return : Z;            (* [comment removed for export] *)
  hl_asan_memset : Z; hl_asan_memcpy : Z; hl_asan_memmove : Z;   (* [comment removed for export] *)
  hl_tp        : Z;                   (* [comment removed for export] *)
  hl_img_lo    : Z; hl_img_hi : Z;    (* [comment removed for export] *)
  hl_rt_static : Z -> Prop;           (* [comment removed for export] *)
  hl_rt_ro     : Z -> Prop;           (* [comment removed for export] *)
  hl_scr_malloc : Z; hl_scr_free : Z; hl_scr_aligned : Z;        (* [comment removed for export] *)
  hl_scr_stack_malloc : Z; hl_scr_no_return : Z; hl_scr_mem : Z; (* [comment removed for export] *)
  hl_k_per_malloc : Z; hl_b_lin : Z; hl_b_overhead : Z;         (* [comment removed for export] *)
  hl_K0 : Z; hl_B0 : Z                (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Record asan_run : Type := AR {
  ar_sptop : Z;                       (* [comment removed for export] *)
  ar_stack_top : Z; ar_stack_bottom : Z;   (* [comment removed for export] *)
  ar_fs : Z;                          (* [comment removed for export] *)
  ar_space_beg : Z                    (* [comment removed for export] *)
}.
Abbreviation ahl_ceil ar := (ar_sptop ar - 8388608).
(* [comment removed for export] *)
Definition app_rng (ar : asan_run) (a n : Z) : Prop :=
  0 <= a /\                                                                                       (* [comment removed for export] *)
  (a + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= a) /\ (a + n <= ar_sptop ar \/ a + n + 16 <= 2 ^ 47).     (* [comment removed for export] *)
Definition FS_BYTES : Z := 0xb09000.

(* [comment removed for export] *)
Definition acredit_ok (L : asan_layout) (cr : credit) (n : Z) : Prop :=
  hl_k_per_malloc L <= fst cr /\ hl_b_lin L * n + hl_b_overhead L <= snd cr.
Definition adebit (L : asan_layout) (cr : credit) (n : Z) : credit :=
  (fst cr - hl_k_per_malloc L, snd cr - (hl_b_lin L * n + hl_b_overhead L)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fframe : Type := (Z * Z * Z)%type.
Definition ff_addr (f : fframe) : Z := fst (fst f).
Definition ff_class (f : fframe) : Z := snd (fst f).
Definition ff_rs (f : fframe) : Z := snd f.
Definition ff_bytes (k : Z) : Z := 64 * 2 ^ k.
(* [comment removed for export] *)
Definition ff_owned (FF : list fframe) (a : Z) : Prop :=
  exists f, In f FF /\ (ff_addr f + 24 <= a < ff_addr f + 32
                        \/ ff_addr f + ff_bytes (ff_class f) - 8 <= a < ff_addr f + ff_bytes (ff_class f)).
Definition in_fframe (FF : list fframe) (a : Z) : Prop :=
  exists f, In f FF /\ ff_addr f <= a < ff_addr f + ff_bytes (ff_class f) - 8 /\ ~ (ff_addr f + 24 <= a < ff_addr f + 32).
Fixpoint ff_remove (F : Z) (FF : list fframe) : list fframe :=
  match FF with
  | [] => []
  | f :: r => if Z.eqb (ff_addr f) F then r else f :: ff_remove F r
  end.
Definition ff_count (k : Z) (FF : list fframe) : nat := length (filter (fun f => Z.eqb (ff_class f) k) FF).
(* [comment removed for export] *)
Definition ff_cap (k : Z) : Z := 2 ^ 20 / ff_bytes k.

(* [comment removed for export] *)
Definition byte_at (M : word -> option byte) (a v : Z) : Prop := M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Definition shadow_zero (M : word -> option byte) (a g : Z) : Prop :=
  forall j, 0 <= j < g -> byte_at M (S a + j) 0.
(* [comment removed for export] *)
Definition shadow_blk (M : word -> option byte) (u n : Z) : Prop :=
  shadow_zero M u (n / 8) /\ (n mod 8 <> 0 -> byte_at M (S u + n / 8) (n mod 8)).
(* [comment removed for export] *)
Definition aacc (M : word -> option byte) (p n : Z) : Prop :=
  forall a, p <= a < p + n -> byte_at M (S a) 0 \/ (exists v, byte_at M (S a) v /\ 1 <= v <= 7 /\ a mod 8 < v).
(* [comment removed for export] *)
Definition in_shadow_of (a n x : Z) : Prop := S a <= x <= S (a + n - 1).

(* [comment removed for export] *)
Definition ablock_range (L : asan_layout) (ar : asan_run) (u n : Z) : Prop :=
  4096 <= u /\ (u + n <= hl_img_lo L \/ hl_img_hi L <= u) /\ u mod 16 = 0 /\ 0 < n /\ u + n <= ahl_ceil ar /\ app_mem u n.
Definition fframes_apart (a n : Z) (FF : list fframe) : Prop :=
  forall f, In f FF -> a + n <= ff_addr f \/ ff_addr f + ff_bytes (ff_class f) <= a.

(* [comment removed for export] *)
Definition block_shadow (LB : list (Z * Z)) (a : Z) : Prop := exists b, In b LB /\ in_shadow_of (fst b) (snd b) a.
Definition aclient_g (BS : Z -> Z -> Z -> Prop) (ST : Z -> Prop) (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scratch : Z) (a : Z) : Prop :=
  in_block LB a
  \/ (ahl_ceil ar <= a < 2 ^ 47 /\ ~ (sp - scratch <= a < sp))
  \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ ST a)
  \/ in_fframe FF a
  \/ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a                            (* [comment removed for export] *)
  \/ (exists f, In f FF /\ in_shadow_of (ff_addr f) (ff_bytes (ff_class f)) a)     (* [comment removed for export] *)
  \/ (exists b, In b LB /\ BS (fst b) (snd b) a).                                  (* [comment removed for export] *)
Definition aclient (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scratch a : Z) : Prop :=
  aclient_g in_shadow_of (hl_rt_static L) L ar LB FF sp scratch a.
Definition aclientw (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scratch a : Z) : Prop :=
  aclient_g (fun _ _ _ => False) (fun x => hl_rt_static L x \/ hl_rt_ro L x) L ar LB FF sp scratch a.
Lemma aclient_g_mono (BS BS' : Z -> Z -> Z -> Prop) (ST ST' : Z -> Prop) L ar LB FF sp scratch a :
  (forall q n x, BS q n x -> BS' q n x) -> (forall x, ST' x -> ST x) -> aclient_g BS ST L ar LB FF sp scratch a -> aclient_g BS' ST' L ar LB FF sp scratch a.
Proof.
  intros H HS [X|[X|[X|[X|[X|[X|X]]]]]]; unfold aclient_g; auto 8.
  - right; right; left. split. exact (proj1 X). intros Y. exact (proj2 X (HS _ Y)).
  - destruct X as (b & Hb & X). do 6 right. exists b. split. exact Hb. apply H. exact X.
Qed.
Lemma aclientw_client L ar LB FF sp scratch a : aclientw L ar LB FF sp scratch a -> aclient L ar LB FF sp scratch a.
Proof. apply aclient_g_mono. intros q n x []. intros x X. left. exact X. Qed.

Definition aheap_pres (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scratch : Z)
           (M M' : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scratch a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall a, sp - scratch <= a < sp -> M' (Z_to_bv 64 a) <> None).

(* [comment removed for export] *)
Definition astack_ok (L : asan_layout) (ar : asan_run) (M : word -> option byte) (scratch sp : Z) : Prop :=
  sp mod 16 = 0 /\ ahl_ceil ar + 4096 + scratch <= sp /\ sp <= ar_sptop ar /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\
  (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= scratch -> store_ok (hl_segs L) M (Z_to_bv 64 (sp - scratch + d)) m = true) /\
  defined M sp (ar_stack_top ar - sp).

(* [comment removed for export] *)
Definition model_rt (m m' : Model) : Prop :=
  m' = mkModelOf (m_fd m) (m_vm m') (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
(* [comment removed for export] *)
Definition vml : Type := (VmMaps * list (word * word))%type.
Definition vml_of (m : Model) : vml := (m_vmmaps m, m_vm_lazy m).

(* [comment removed for export] *)
Definition shadow_allowed (A : list (Z * Z)) (a n : Z) : Prop :=
  forall x, in_shadow_of a n x -> page_allowedb A (page_base (Z_to_bv 64 x)) = true.
(* [comment removed for export] *)
Definition ahid (A : list (Z * Z)) (m : Model) : word -> bool := mkH (m_vm_lazy m) A.

(* [comment removed for export] *)
Record asan_statics_cells : Type := ASC {
  asc_got_lo : Z; asc_got_hi : Z;     (* [comment removed for export] *)
  asc_cells : list (Z * Z * Z)        (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition cell_is (segs : list Segment) (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Definition asan_statics (segs : list Segment) (C : asan_statics_cells) (M : word -> option byte) : Prop :=
  (forall a, asc_got_lo C <= a < asc_got_hi C -> M (Z_to_bv 64 a) = None)
  /\ Forall (fun c => cell_is segs M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) (asc_cells C).

(* [comment removed for export] *)
Section AIface.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.       (* [comment removed for export] *)

Record asan_iface : Type := AI {
  ri_inv : list (Z * Z) -> list fframe -> list fframe -> credit -> list (Z * Z) -> (word -> option byte) -> vml -> Prop
}.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

(* [comment removed for export] *)
Definition amalloc_post (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet) : Prop :=
  forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)) (u : Z),
    getr R' 10%bv = Z_to_bv 64 u ->
    regs_preserved R R' ->
    ablock_range L ar u n -> blocks_apart u n LB -> fframes_apart u n (FF ++ LK) ->
    defined M' u n -> shadow_blk M' u n ->
    aheap_pres L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_malloc L) M M' ->
    model_rt model model' -> incl A A' -> MInv A' model' ->
    ri_inv HI ((u, n) :: LB) FF LK (adebit L cr n) A' M' (vml_of model') ->
    srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K.

Definition amalloc_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> acredit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_malloc L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    amalloc_post fx R M model LB FF LK cr A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.

Definition aaligned16_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= 4096 -> n mod 16 = 0 -> acredit_ok L cr n ->       (* [comment removed for export] *)
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_aligned L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)) (u : Z),
        getr R' 10%bv = Z_to_bv 64 u ->
        regs_preserved R R' ->
        ablock_range L ar u n -> blocks_apart u n LB -> fframes_apart u n (FF ++ LK) ->
        defined M' u n -> shadow_blk M' u n ->
        aheap_pres L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_aligned L) M M' ->
        model_rt model model' -> incl A A' -> MInv A' model' ->
        ri_inv HI ((u, n) :: LB) FF LK (adebit L cr n) A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_aligned_alloc L)) M model) K.

Definition afree_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (u n : Z) (K : ShapeAlg.TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    In (u, n) LB -> getr R 10%bv = Z_to_bv 64 u ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_free L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
        regs_preserved R R' ->
        aheap_pres L ar (lb_remove u LB) FF (bv_unsigned (getr R 2%bv)) (hl_scr_free L) M M' ->
        model_rt model model' -> incl A A' -> MInv A' model' ->
        ri_inv HI (lb_remove u LB) FF LK cr A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_free L)) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ff_room (k : Z) (FF LK : list fframe) : Prop := Z.of_nat (ff_count k (FF ++ LK)) + 2 <= ff_cap k.

Definition astack_malloc_spec (k : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_stack_malloc L) sp ->
    ff_room k FF LK ->
    (forall f, In f FF -> sp + 32 <= ff_rs f) ->                    (* [comment removed for export] *)
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (F fl : Z) (LK' : list fframe),
        getr R' 10%bv = Z_to_bv 64 F ->
        regs_preserved R R' ->
        ar_fs ar <= F /\ F + ff_bytes k <= ar_fs ar + FS_BYTES /\ F mod ff_bytes k = 0 /\ app_mem F (ff_bytes k) /\ F + ff_bytes k <= ahl_ceil ar ->
        (F + ff_bytes k <= hl_img_lo L \/ hl_img_hi L <= F) ->
        fframes_apart F (ff_bytes k) (FF ++ LK') -> (forall b, In b LB -> F + ff_bytes k <= fst b \/ fst b + snd b <= F) ->
        incl LK' LK ->                                              (* [comment removed for export] *)
        defined M' F (ff_bytes k) ->
        cell_is (hl_segs L) M' (F + ff_bytes k - 8) 8 fl ->                 (* [comment removed for export] *)
        ar_fs ar <= fl < ar_fs ar + FS_BYTES -> ~ aclient L ar LB ((F, k, sp + 32) :: FF) 0 0 fl ->          (* [comment removed for export] *)
        (F + ff_bytes k <= fl \/ fl + 1 <= F) ->                   (* [comment removed for export] *)
        store_ok (hl_segs L) M' (Z_to_bv 64 fl) 1 = true ->
        shadow_zero M' F (ff_bytes k / 8) ->                        (* [comment removed for export] *)
        aheap_pres L ar LB FF sp (hl_scr_stack_malloc L) M M' ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB ((F, k, sp + 32) :: FF) LK' cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_stack_malloc L k)) M model) K.

(* [comment removed for export] *)
Definition rt_release_frame : Prop :=
  forall LB FF LK cr A M M' V F k rs fl,
    ri_inv HI LB FF LK cr A M V -> In (F, k, rs) FF -> cell_is (hl_segs L) M (F + ff_bytes k - 8) 8 fl ->
    (forall a, 0 <= a < 2 ^ 64 -> a <> fl -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) \/ aclientw L ar LB FF 0 0 a) ->      (* [comment removed for export] *)
    cell_is (hl_segs L) M' fl 1 0 -> (forall a : word, M a <> None -> M' a <> None) ->
    ri_inv HI LB (ff_remove F FF) LK cr A M' V.
(* [comment removed for export] *)
Definition rt_flagptr : Prop :=
  forall LB FF LK cr A M V LB' FF' LK' cr' A' M' V' F k rs rs' fl,
    ri_inv HI LB FF LK cr A M V -> ri_inv HI LB' FF' LK' cr' A' M' V' ->
    In (F, k, rs) FF -> In (F, k, rs') FF' ->
    cell_is (hl_segs L) M (F + ff_bytes k - 8) 8 fl -> cell_is (hl_segs L) M' (F + ff_bytes k - 8) 8 fl.
(* [comment removed for export] *)
Definition rt_leak_frames : Prop :=
  forall LB FF LK cr A M V FX,
    ri_inv HI LB FF LK cr A M V -> incl FX FF -> NoDup (map ff_addr FX) ->
    ri_inv HI LB (filter (fun f => negb (existsb (fun g => Z.eqb (ff_addr g) (ff_addr f)) FX)) FF) (FX ++ LK) cr A M V.

(* [comment removed for export] *)
Definition ahandle_no_return_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_no_return L) sp ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (lo : Z),
        regs_preserved R R' ->
        sp - hl_scr_no_return L - 4096 <= lo <= sp -> lo mod 4096 = 0 ->       (* [comment removed for export] *)
        shadow_zero M' lo ((ar_stack_top ar - lo) / 8) ->          (* [comment removed for export] *)
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp (hl_scr_no_return L) a ->
                   ~ in_shadow_of lo (ar_stack_top ar - lo) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - hl_scr_no_return L <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_handle_no_return L)) M model) K.

(* [comment removed for export] *)
Definition amem_post (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dst n : Z)
           (NEWB : Z -> Z -> Prop) (K : ShapeAlg.TSet) : Prop :=
  forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
    getr R' 10%bv = Z_to_bv 64 dst -> regs_preserved R R' ->
    (forall i, 0 <= i < n -> exists v, NEWB i v /\ byte_at M' (dst + i) v) ->
    (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) a ->
               ~ (dst <= a < dst + n) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a, bv_unsigned (getr R 2%bv) - hl_scr_mem L <= a < bv_unsigned (getr R 2%bv) -> M' (Z_to_bv 64 a) <> None) ->
    model_rt model model' -> MInv A model' ->
    ri_inv HI LB FF LK cr A M' (vml_of model') ->
    srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K.

Definition amem_pre (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dst n : Z) (K : ShapeAlg.TSet) : Prop :=
  ri_inv HI LB FF LK cr A M (vml_of model) /\ m_halted model = None /\ MInv A model /\
  getr R 10%bv = Z_to_bv 64 dst /\ getr R 12%bv = Z_to_bv 64 n /\ 0 <= n <= 2 ^ 27 /\
  getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ Hoare.ret_ok (getr R 1%bv) /\
  astack_ok L ar M (hl_scr_mem L) (bv_unsigned (getr R 2%bv)) /\
  aacc M dst n /\ (forall i, 0 <= i < n -> aclientw L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (dst + i)) /\   (* [comment removed for export] *)
  (forall i (m : nat), 0 <= i -> i + Z.of_nat m <= n -> store_ok (hl_segs L) M (Z_to_bv 64 (dst + i)) m = true) /\
  K [] /\ app_rng ar dst n.                                            (* [comment removed for export] *)

Definition amemset_spec : Prop :=
  forall fx R M model LB FF LK cr A dst c n K,
    amem_pre fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 c ->
    amem_post fx R M model LB FF LK cr A dst n (fun _ v => v = c mod 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_asan_memset L)) M model) K.

Definition amemcpy_spec_at (pc : Z) (may_overlap : bool) : Prop :=
  forall fx R M model LB FF LK cr A dst src n (bs : list byte) K,
    amem_pre fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 src ->
    aacc M src n -> 0 <= src /\ src + n <= 2 ^ 47 -> app_rng ar src n ->       (* [comment removed for export] *)
    (forall i, 0 <= i < n -> hl_img_lo L <= src + i < hl_img_hi L \/ aclient L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (src + i)) ->
                                                                          (* [comment removed for export] *)
    rdn (hl_segs L) M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->          (* [comment removed for export] *)
    (may_overlap = false -> dst + n <= src \/ src + n <= dst) ->
    amem_post fx R M model LB FF LK cr A dst n (fun i v => nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.
Definition amemcpy_spec : Prop := amemcpy_spec_at (hl_asan_memcpy L) false.
Definition amemmove_spec : Prop := amemcpy_spec_at (hl_asan_memmove L) false.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_private (LB : list (Z * Z)) (FF : list fframe) (a : Z) : Prop :=
  ~ aclient L ar LB FF 0 0 a \/ hl_rt_ro L a \/ block_shadow LB a.        (* [comment removed for export] *)

Definition rt_frame : Prop :=
  forall LB FF LK cr A M M' V,
    ri_inv HI LB FF LK cr A M V ->
    (forall a, 0 <= a < 2 ^ 64 -> art_private LB FF a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    ri_inv HI LB FF LK cr A M' V.

Definition rt_wf : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    (forall b, In b LB -> ablock_range L ar (fst b) (snd b) /\ defined M (fst b) (snd b) /\ shadow_blk M (fst b) (snd b)
                       /\ shadow_allowed A (fst b) (snd b)
                       /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB) /\ fframes_apart (fst b) (snd b) (FF ++ LK)
                       /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b))         (* [comment removed for export] *)
    /\ (forall f, In f FF -> ar_fs ar <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs ar + FS_BYTES
                       /\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) [1; 2; 3]
                       /\ defined M (ff_addr f) (ff_bytes (ff_class f))
                       /\ fframes_apart (ff_addr f) (ff_bytes (ff_class f)) (ff_remove (ff_addr f) FF ++ LK))
    /\ app_mem (ar_fs ar) FS_BYTES /\ ar_fs ar + FS_BYTES <= ahl_ceil ar /\ (ar_fs ar + FS_BYTES <= hl_img_lo L \/ hl_img_hi L <= ar_fs ar)
    /\ shadow_allowed A (ar_fs ar) FS_BYTES
    /\ shadow_allowed A (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar)
    /\ (ahl_ceil ar <= ar_stack_bottom ar + 4096 /\ ar_stack_bottom ar <= ahl_ceil ar + 4096)   (* [comment removed for export] *)
    /\ (ar_stack_bottom ar mod 4096 = 0 /\ ar_stack_top ar = ar_stack_bottom ar + 8388608
        /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\ ar_sptop ar mod 16 = 0)     (* [comment removed for export] *)
    /\ ar_stack_top ar <= 2 ^ 47
    /\ NoDup (map fst LB) /\ NoDup (map ff_addr (FF ++ LK)) /\ 0 <= fst cr /\ 0 <= snd cr
    /\ defined M (ar_fs ar) FS_BYTES.                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_lazy : Prop :=
  forall LB FF LK cr A M model, ri_inv HI LB FF LK cr A M (vml_of model) ->
    A_wf A
    /\ (forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
          let a := bv_unsigned w in
          hl_img_hi L <= a /\ a < ahl_ceil ar /\ ~ in_block LB a /\ ~ (ar_fs ar <= a < ar_fs ar + FS_BYTES)).

Definition rt_perm : Prop :=
  forall LB LB' FF FF' LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    (forall b, In b LB <-> In b LB') -> NoDup (map fst LB') -> (forall f, In f FF <-> In f FF') -> NoDup (map ff_addr FF') ->
    ri_inv HI LB' FF' LK cr A M V.

(* [comment removed for export] *)
Definition rt_small_high : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V -> forall b, In b LB -> snd b <= 4096 -> BIGSHADOW_HI <= fst b.

Definition rt_statics : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V -> asan_statics (hl_segs L) C M.

(* [comment removed for export] *)
Record asan_iface_ok : Prop := AIOK {
  aio_malloc : amalloc_spec;
  aio_aligned : aaligned16_spec;
  aio_free : afree_spec;
  aio_stack_malloc : forall k, In k [1; 2; 3] -> astack_malloc_spec k;
  aio_release : rt_release_frame;
  aio_leak : rt_leak_frames;
  aio_no_return : ahandle_no_return_spec;
  aio_memset : amemset_spec;
  aio_memcpy : amemcpy_spec;
  aio_memmove : amemmove_spec;
  aio_frame : rt_frame;
  aio_wf : rt_wf;
  aio_lazy : rt_lazy;
  aio_perm : rt_perm;
  aio_statics : rt_statics;
  aio_flagptr : rt_flagptr;         (* [comment removed for export] *)
  aio_small_high : rt_small_high    (* [comment removed for export] *)
}.
End AIface.

(* [comment removed for export] *)

End HeapIfaceA.
Module HeapIfaceANull.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition afree_null_spec (L : asan_layout) (ar : asan_run) (scfg : SpuriousCfg) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 0 ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_free L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
        regs_preserved R R' ->
        aheap_pres L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_free L) M M' ->
        model_rt model model' -> incl A A' -> MInv A' model' ->
        ri_inv HI LB FF LK cr A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

End HeapIfaceANull.
From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions.
Module HeapIfaceAMx.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceANull OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section AIfaceB.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.
Record asan_iface_okB : Prop := AIOKB {
  aiob_malloc : amalloc_spec L ar scfg HI;
  aiob_aligned : aaligned16_spec L ar scfg HI;
  aiob_free : afree_spec L ar scfg HI;
  aiob_stack_malloc : forall k, In k [1; 3] -> astack_malloc_spec L ar scfg HI k;
  aiob_release : rt_release_frame L ar HI;
  aiob_leak : rt_leak_frames HI;
  aiob_no_return : ahandle_no_return_spec L ar scfg HI;
  aiob_memset : amemset_spec L ar scfg HI;
  aiob_memcpy : amemcpy_spec L ar scfg HI;
  aiob_memmove : amemmove_spec L ar scfg HI;
  aiob_frame : rt_frame L ar HI;
  aiob_wf : rt_wf L ar HI;
  aiob_lazy : rt_lazy L ar HI;
  aiob_perm : rt_perm HI;
  aiob_statics : rt_statics L C HI;
  aiob_flagptr : rt_flagptr L HI;
  aiob_small_high : rt_small_high HI
}.
End AIfaceB.

Module HAJ.

(* [comment removed for export] *)
Definition ann_shadow (M : word -> option byte) (b u c : Z) : Prop :=
  shadow_zero M b (u / 8) /\ (u mod 8 <> 0 -> byte_at M (S b + u / 8) (u mod 8))
  /\ (forall j, (u + 7) / 8 <= j < (c + 7) / 8 -> byte_at M (S b + j) 252).
(* [comment removed for export] *)
Definition shadow_blkR (M : word -> option byte) (u n : Z) : Prop :=
  shadow_blk M u n \/ (exists m, 0 <= m <= n /\ ann_shadow M u m n).

Lemma shadow_blkR_of (M : word -> option byte) u n : shadow_blk M u n -> shadow_blkR M u n.
Proof. intros H. left. exact H. Qed.

(* [comment removed for export] *)
Lemma ann_shadow_full (M : word -> option byte) b c : 0 <= c -> ann_shadow M b c c <-> shadow_blk M b c.
Proof.
  intros Hc. unfold ann_shadow, shadow_blk. split.
  - intros (Z0 & P & _). split; [exact Z0 | exact P].
  - intros (Z0 & P). split; [exact Z0 | split; [exact P | intros j Hj; lia]].
Qed.

(* [comment removed for export] *)
Definition atexit_cells (segs : list Segment) (M : word -> option byte) (X f0 a0 f1 a1 atc : Z) (hs : list (Z * Z)) : Prop :=
  L5.u8_at segs M X 0 /\ L5.u32_at segs M (X + 4) 0 /\ L5.u32_at segs M (X + 8) (2 + 2 * Z.of_nat (length hs))
  /\ L5.u64_at segs M (X + 16) (X + 24) /\ L5.u64_at segs M (X + 24) 0
  /\ L5.u64_at segs M (X + 32) f0 /\ L5.u64_at segs M (X + 288) a0
  /\ L5.u64_at segs M (X + 40) f1 /\ L5.u64_at segs M (X + 296) a1
  /\ (forall (i : nat) f a, nth_error hs i = Some (f, a) ->
        L5.u64_at segs M (X + 48 + 16 * Z.of_nat i) f /\ L5.u64_at segs M (X + 56 + 16 * Z.of_nat i) atc
        /\ L5.u64_at segs M (X + 304 + 16 * Z.of_nat i) a /\ L5.u64_at segs M (X + 312 + 16 * Z.of_nat i) 0).

(* [comment removed for export] *)
Record ext_consts : Type := EXTC {
  ec_ann_pc : Z; ec_ann_scr : Z;          (* [comment removed for export] *)
  ec_cxa_pc : Z; ec_cxa_scr : Z;          (* [comment removed for export] *)
  ec_atexit : Z; ec_f0 : Z; ec_a0 : Z;              (* [comment removed for export] *)
  ec_f1 : Z; ec_a1 : Z;                               (* [comment removed for export] *)
  ec_atc : Z;                                        (* [comment removed for export] *)
  ec_nl : Z;                                         (* [comment removed for export] *)
  ec_sf_pc : Z; ec_sf_scr : Z             (* [comment removed for export] *)
}.

Section X.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

(* [comment removed for export] *)
Definition rt_wfR : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    (forall b, In b LB -> ablock_range L ar (fst b) (snd b) /\ defined M (fst b) (snd b) /\ shadow_blkR M (fst b) (snd b)
                       /\ shadow_allowed A (fst b) (snd b)
                       /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB) /\ fframes_apart (fst b) (snd b) (FF ++ LK)
                       /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b))
    /\ (forall f, In f FF -> ar_fs ar <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs ar + FS_BYTES
                       /\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) [0; 1; 2; 3; 4; 5]
                       /\ defined M (ff_addr f) (ff_bytes (ff_class f))
                       /\ fframes_apart (ff_addr f) (ff_bytes (ff_class f)) (ff_remove (ff_addr f) FF ++ LK))
    /\ app_mem (ar_fs ar) FS_BYTES /\ ar_fs ar + FS_BYTES <= ahl_ceil ar /\ (ar_fs ar + FS_BYTES <= hl_img_lo L \/ hl_img_hi L <= ar_fs ar)
    /\ shadow_allowed A (ar_fs ar) FS_BYTES
    /\ shadow_allowed A (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar)
    /\ (ahl_ceil ar <= ar_stack_bottom ar + 4096 /\ ar_stack_bottom ar <= ahl_ceil ar + 4096)
    /\ (ar_stack_bottom ar mod 4096 = 0 /\ ar_stack_top ar = ar_stack_bottom ar + 8388608
        /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\ ar_sptop ar mod 16 = 0)
    /\ ar_stack_top ar <= 2 ^ 47
    /\ NoDup (map fst LB) /\ NoDup (map ff_addr (FF ++ LK)) /\ 0 <= fst cr /\ 0 <= snd cr
    /\ defined M (ar_fs ar) FS_BYTES.

(* [comment removed for export] *)
Record asan_iface_okR : Prop := AIOKR {
  aior_malloc : amalloc_spec L ar scfg HI;
  aior_aligned : aaligned16_spec L ar scfg HI;
  aior_free : afree_spec L ar scfg HI;
  aior_stack_malloc : forall k, In k [0; 1; 2; 3; 4; 5] -> astack_malloc_spec L ar scfg HI k;
  aior_release : rt_release_frame L ar HI;
  aior_leak : rt_leak_frames HI;
  aior_no_return : ahandle_no_return_spec L ar scfg HI;
  aior_memset : amemset_spec L ar scfg HI;
  aior_memcpy : amemcpy_spec L ar scfg HI;
  aior_memmove : amemmove_spec L ar scfg HI;
  aior_frame : rt_frame L ar HI;
  aior_wf : rt_wfR;
  aior_lazy : rt_lazy L ar HI;
  aior_perm : rt_perm HI;
  aior_statics : rt_statics L C HI;
  aior_flagptr : rt_flagptr L HI;
  aior_small_high : rt_small_high HI
}.

(* [comment removed for export] *)
Definition annotate_spec (pc scr : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet) (b c u u' : Z),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 b -> getr R 11%bv = Z_to_bv 64 (b + c) -> getr R 12%bv = Z_to_bv 64 (b + u) -> getr R 13%bv = Z_to_bv 64 (b + u') ->
    In (b, c) LB -> b mod 16 = 0 -> 0 <= u <= c -> 0 <= u' <= c ->
    ann_shadow M b u c ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M scr sp ->
    K [] ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
        regs_preserved R R' ->
        ann_shadow M' b u' c ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> ~ in_shadow_of b c a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, in_shadow_of b c a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
        (forall a, sp - scr <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        model_rt model model' -> incl A A' -> MInv A' model' ->
        ri_inv HI LB FF LK cr A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx' R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.

(* [comment removed for export] *)
Definition cxa_atexit_spec (pc scr X f0 a0 f1 a1 atc nl : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet) (hs : list (Z * Z)) (f a d : Z),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 f -> getr R 11%bv = Z_to_bv 64 a -> getr R 12%bv = Z_to_bv 64 d ->
    (length hs <= 2)%nat -> atexit_cells (hl_segs L) M X f0 a0 f1 a1 atc hs -> L5.u8_at (hl_segs L) M nl 0 ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M scr sp ->
    K [] ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 0 ->
        atexit_cells (hl_segs L) M' X f0 a0 f1 a1 atc (hs ++ [(f, a)]) ->
        (forall x, 0 <= x < 2 ^ 64 -> aclient L ar LB FF sp scr x -> ~ (X <= x < X + 544) -> M' (Z_to_bv 64 x) = M (Z_to_bv 64 x)) ->
        (forall x, X <= x < X + 544 -> M (Z_to_bv 64 x) <> None -> M' (Z_to_bv 64 x) <> None) ->
        (forall x, sp - scr <= x < sp -> M' (Z_to_bv 64 x) <> None) ->
        model_rt model model' -> incl A A' -> MInv A' model' ->
        ri_inv HI LB FF LK cr A' M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx' R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.

(* [comment removed for export] *)
Definition astack_free_spec (pc scr k : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet) (F rs : Z),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    In (F, k, rs) FF ->
    getr R 10%bv = Z_to_bv 64 F ->                   (* [comment removed for export] *)
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M scr sp ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        (forall j, 0 <= j < ff_bytes k / 8 -> byte_at M' (S F + j) 245) ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> ~ in_shadow_of F (ff_bytes k) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - scr <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB (ff_remove F FF) LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.

(* [comment removed for export] *)
Definition rt_frame_ctr : Prop :=
  forall LB FF LK cr A M M' V, ri_inv HI LB FF LK cr A M V ->
    (forall a, 0 <= a < 2 ^ 64 -> art_private L ar LB FF a -> ~ (hl_tp L + 16 <= a < hl_tp L + 20) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    cell_is (hl_segs L) M' (hl_tp L + 16) 4 0 -> (forall a : word, M a <> None -> M' a <> None) -> ri_inv HI LB FF LK cr A M' V.

(* [comment removed for export] *)
Record asan_ext_ok (E : ext_consts) : Prop := AEXT {
  aex_annotate : annotate_spec (ec_ann_pc E) (ec_ann_scr E);
  aex_cxa_atexit : cxa_atexit_spec (ec_cxa_pc E) (ec_cxa_scr E) (ec_atexit E) (ec_f0 E) (ec_a0 E) (ec_f1 E) (ec_a1 E) (ec_atc E) (ec_nl E);
  aex_frame_ctr : rt_frame_ctr;
  aex_free_null : afree_null_spec L ar scfg HI;
  aex_stack_free : astack_free_spec (ec_sf_pc E) (ec_sf_scr E) 5          (* [comment removed for export] *)
}.
End X.

(* [comment removed for export] *)
Definition strict_of (HIR : asan_iface) : asan_iface :=
  AI (fun LB FF LK cr A M V => ri_inv HIR LB FF LK cr A M V /\ Forall (fun b => shadow_blk M (fst b) (snd b)) LB
                               /\ Forall (fun f => In (ff_class f) [1; 2; 3]) (FF ++ LK)).

End HAJ.

End HeapIfaceAMx.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module HeapIfaceAMr.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceANull OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_HeapIfaceAMr () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List4inclc59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C45stdpp;list_basics4list;list_filterC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC35stdpp4base6FilterC46Stdlib5Lists4List7existsbI35stdpp4base5NoDup00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00c59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02c59OSSVerify5KrLib7Mh_0089:HeapIfaceA7cell_isC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic3and00C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic6eq_indC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums1N00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib6ZArith:ZArith_dec8Z_lt_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6eq_decK47Corelib4Init5Logic3and01K47Corelib4Init6Specif7sumbool01C47Corelib4Init5Logic9False_indK47Corelib4Init6Specif7sumbool02c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR6fvalidC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indI47Corelib4Init5Logic5False00K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01i69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR6rchain00C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR6rchain01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr04c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR=cell_is_agreeC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR6rchain02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR:fvalid_decC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR6rchain03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR:rchain_indC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR<rchain_frameC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init9Datatypes7nat_indc69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR4ukeyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR4akeyC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC46Stdlib5Lists4List>existsb_existsc69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR3kinC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;list_eq_decK47Corelib4Init9Datatypes4bool02C47Corelib7Classes>Morphisms_PropIiff_iff_iff_impl_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveK47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC47Corelib7Classes>Morphisms_Prop@and_iff_morphismc69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR6kin_InC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_lec69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR7warm_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR5NW_LOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR5NW_HIC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3sndc69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR=amalloc_postGC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA:shadow_blkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA=hl_scr_mallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA:aheap_presC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR9fr_weakenC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR;afree_postGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA;hl_scr_freeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR7fr_baseC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR<amalloc_preGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR=hlr_pc_mallocC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR7ukey_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA:acredit_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA6adebitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR=warm_ok_factsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedc59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA9astack_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR=credit_nonnegC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HARCamalloc_postG_knownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR:fr_mallocWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR:fr_mallocLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR4NREQC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR=amallocU_specC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR:afree_preGC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR;hlr_pc_freeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_freeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HARAafree_postG_knownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR8fr_freeWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR8fr_freeLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR;afreeU_specC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module HAR.

(* [comment removed for export] *)
Definition NREQ : Z := 2 ^ 30.           (* [comment removed for export] *)
Definition NW_LO : Z := 64.              (* [comment removed for export] *)
Definition NW_HI : Z := 128.
(* [comment removed for export] *)
Record layoutR : Type := LR { hlr_pc_malloc : Z; hlr_pc_free : Z }.

(* [comment removed for export] *)
Section Chain.
Variable L : asan_layout.
Variable ar : asan_run.

(* [comment removed for export] *)
Definition fvalid (lo fp : Z) : Prop := lo < fp /\ fp < ar_stack_top ar - 16 /\ fp mod 8 = 0.

(* [comment removed for export] *)
Inductive rchain (M : word -> option byte) : Z -> Z -> list Z -> Prop :=
| rc_stop : forall lo fp, ~ fvalid lo fp -> rchain M lo fp []
| rc_low  : forall lo fp pc1, fvalid lo fp -> cell_is (hl_segs L) M (fp - 8) 8 pc1 -> 0 <= pc1 < 4096 -> rchain M lo fp []
| rc_cons : forall lo fp ra fp' RC, fvalid lo fp ->
              cell_is (hl_segs L) M (fp - 8) 8 ra -> 4096 <= ra < 2 ^ 64 ->
              cell_is (hl_segs L) M (fp - 16) 8 fp' -> 0 <= fp' < 2 ^ 64 ->
              rchain M fp fp' RC -> rchain M lo fp (ra :: RC).

(* [comment removed for export] *)
Definition akey (p0 : Z) (RC : list Z) : list Z := p0 :: firstn 29 (filter (fun x => negb (x =? p0)) RC).

(* [comment removed for export] *)
Definition ukey (p0 : Z) (M : word -> option byte) (sp ra s0 : Z) (K : list Z) : Prop :=
  (~ fvalid (ar_stack_bottom ar) sp /\ K = [p0])
  \/ (fvalid (ar_stack_bottom ar) sp /\ 0 <= ra < 4096 /\ K = [p0])
  \/ (fvalid (ar_stack_bottom ar) sp /\ 4096 <= ra < 2 ^ 64 /\ s0 <> sp + 8 /\ exists RC, rchain M sp s0 RC /\ K = akey p0 (ra :: RC)).
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cell_is_agree (M M' : word -> option byte) a v :
  0 <= a -> a + 8 < 2 ^ 64 -> (forall x : word, a <= bv_unsigned x < a + 8 -> M' x = M x) ->
  cell_is (hl_segs L) M a 8 v -> cell_is (hl_segs L) M' a 8 v.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Chain"] "h01xh14__x1h27__arithh36__sat0h46__sat1h52Hah62Hxh74__ffh88__varmaph95__with:1mh;1nh<1zh=1Mh>2M'h?4__x2h@1ahA1vhB1yhC2AGhD1ChE1HhF2H0hG2H1hH2H2hI2H3hJ2HbhK3Hx0hL6__sat2hM1ohN1qhO1rp&0p;1p;2p;3p;5p;4p;6p;<p;7p;8p;Bp-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj1<Tg009Tj1]Tg00:2j1QTg00:Uj1MTg00;7j1GTg00;UR6j21Tg00<2R0j2=Tg00<OR4j20Tg00<kj27Tg00=Uj3:Tg00=oj1dTg00>nj18Tg00?Mj5`Tg00@Lj1\Tg00@lj2@Tg00ARj4ZTg00BCj2YTg00BiR5j1XTg00CIR7j26Tg00Cej2~Tg00DMj3qTg00E1j1nTg00EQj2RTg00Eoj1lTg00FMj1jTg00G8j2VTg00G[j2CTg00H>j3hTg00Haj3gTg00IDj1fTg00Ifj2eTg00JHj2>Tg00Jbj2cTg00KNj3bTg00Kmk405Tg00L_R2j1aTg00M=R3j23Tg00M]j29Tg00N8j3_Tg00N^j1^Tg00O<j6DTg00Oej4KTg00PPj3LTg00Q3j6PTg00QQj2NTg00R@j6ATg00R\l<WTg00SAk400Tg00Shj3}Tg00TYj2yTg00U:j1wTg00USj2JTg00V0j2pTg00VMj2oTg00W4j2rTg00W[j2sTg00XAj2tTg00Xgj1mTg00YEj4uTg00Ycj7vTg00ZXj2kTg00[`j2xTg00\Bj4UTg00\mj7zTg00]Qj8{Tg00^5j4|Tg00^Xl<OTg00_=lBFTg00_cj7iTg00`GR1f0R8'6p=5f3R9f2R:'6f1R;/08'9p=4g00`eR<P;g00aCP8CUp=BP;g00ajR=g00bIR>P>g00biR?P8g00cIFzp=;P<P;g00ciP8CUp=EP9P=P>P>P?P:P;P8G{p=?1><8p=2P<P<g00dPP8C|p=Hg00e4R@P<P<P<P2P2f5R2f4RAP9P:P;P8M<Op>04P<P<P<P<P<P<P0P8P;P:P0P9PAP2f6R0f7RBf8RCf9RDMBFp=[P<P<P4PBP4P0P2PAP9P:P;P8M<Wp=IP:P=P>P>P?P;P8Fip=S10;8,9:p=TP<P<P<P<P<P<P3P8P;P:P3P9PAP2P0PBPCPDMBFp>03g00eRR3P<P<P<P5P5P2PAP9P:P;P8M<Op>02P<P<P<P<P<P<P6P8P;P:P6P9PAP2P0PBPCPDMBFp>01g00f1R6#<R5#<#<R=#<#<#<R4#]RE#QRF%]=#QRG#MRH[RI%5;RJ%G=R=,1:%G5RK%G4R4'=RL'0PA17E8RMPM11A=C4P0P;O1PBP;O15:H[^0Fp,1L#dRHP0PAg00fV#8#8#8#8#8#8#8#8RNP9D`%\GRG#MROPHPB1@E2RPPNCZPHPB1@E0RQPNCZ=:O8XMOPHPNP0PBPPP<1YE2RO%XNRR,18RS/6LX<<RTP<P2PT1~K4RT101K%54101LRU[[RV%5KRWg00g5RXAqK4;UW5RY%5LRZ\X^5WRWg00gQRX#nR[%\XRX1R<;R\%l<R]%j<R^1V<6R61C<=5h<R_1C<K=g<ER`'B,;^Ra%f>R>1E_`,;^C?1e^?R?P8P:g00h=Rbg00h]Rc'>1c8:=:bcdAb<1;H05Rcb7b8b9X1<118=Rb/0LRd11;=Re/6L[^1<P8PCP2O2b2b3b4%aERf,=KRg,32%52Rh102gRi'9102LRj,9hPhPiPhPjp-0Rj/>h9_hhP8X0<Rh10;8#^XB<X0<RiP2P2%22PgPLPhPhPh1=;8#H#2X:<X;<RkPKPK%2KRlPfP4PhPh%a8#2X0@PEP4%24J04R@M:[RmGIEDPTPVPYPWP[PXP\P]P^PaP>P^1C<1/E6,;^RaP>1B6`,;^9S^aC?C?P?Pcb7b8b9X1<Ra%5:?T:L\J\d^1<RdP8PCP2P0O3b2b3b4CK9L2gEP11OR/6Le17EP1NE2EP17EQRQPMPM11QRC4P9P;P<1@EB,7EP817E:RQPQPSC4X<<P81YEBRM1NEBEAPM17E;RPPP11MRC4P<13CgRMP817E9RPPPPSC4X<<P8PC%5CRS10CgRP'910CLRO,9SPSPPPSPO1>jS9_SSPhPiPCPC%2CRSPgPLPmGIED16MQRm11MRRj,0QRO'913CLRPPQPQ11P=C4RPPmPOPhP4O1R4,=KRO,3CRm/6QPhP=O1RJ,1mR`,0QP<P<P7PhP716;8#^XB<X0<PMPmPhPhPh13;8#H#2X:<X;<PCPCPSPgPOPhPhPhPkPKPKPlPfP4P@M:[N:03R@PQPQ%2QR4M<WPhPiPQPQP4PjP`PhPhPh11;8#H#2X:<X;<PMPmP@PRPJPhPh%X8#2X03PNP=%2=J02N:01GIEDP8H00PPA}DLBf:/3L#5\ZPTPVPYPWf<RZ/yLA:<L1RD#wf=RB1JBL,pL13BL'15:<[1oBLf>RB/3LRP#5?TPL\U1rBL10L1f?RB/3LRU,0L16U1'9[1sBLf@RB/JL=:<1\D1tBLfARB/3L=:<B\D1JBLP<fBRD/3LP<PaPdP8fDPBPDO3b2bObNbIbHbGbFbEb3b4bLbKCK9LCgEAPCPQPQ11CRC4PTPVPYPWP[PXP<1R<:P;%m<CuP]P^1V<5R5,E6,;^1B5_,;^5S^R^P>P^C?P?Pcb7b8b9X1<X?<P8P;P;PbC4P;P:P:PeC4[^1<^?<P817E0PZP9O3b2b3b4b6b6O2W6X0FFv1@EA,kN,xGP8EAPHP0P2PNPAD`eWDWCWJW5XA<X@<X>IX=IP9P:P;P8O4XA<X@<X>IW=o"). Qed.

Lemma fvalid_dec lo fp : {fvalid lo fp} + {~ fvalid lo fp}.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Chain"] "p'0h01Hh12H1h22H0h32H2h41ni001nh51si011sh62fph72loh81ei021eh91li031lh:2l0p;2p;1p;4p;3p;5p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g00i=j29Tg00<Oj21Tg00U:j10Tg00iaR6j25Tg00jAj1ETg008oj17Tg00;7j1;Tg00kEj2?Tg00M]j24Tg00M=j2:Tg00kbj2>Tg00lBj4=Tg00l]j3CTg00m=j2ATg00m\j38Tg00n<j2@Tg00=Uj3<Tg00o@j5BTg00`eR0f1R4f0R5':g00`GR73<p=2f2R2/14/45p=3A<057p=Df3R3P2g00o]R1P4P5DBp=619451145R8%08'5P61124R8%081132R8p,2ar#Eg00f1#7#7#7R9#7#;'?R:%;9R9,22532'4R2%02'5P5193:113:R2%02'5P6f4R;/1:R<%0<f6R=f5R>11>:R?12>9'4R@33RA%0A'5P51:=9RA/>7%DARA%0A'5P6f7R6/29R7%07f9RBf8RC12C9RD93C:RE33RF%0F'5P5f:RF/1BRG11B:RH12B9RB'4RI'4RJ%0JRKPGPIP=PHPBP3P5C=C=3CX8DP5O1%0Df;RD/1FRI12F9RG93F:12D993D:f<RD/1:RF12D9f=/29P>P5O1P11A15RDb1W3X0FP5C6W1X2IP5C6X0JPKe98JKW4P5O1n200110100021010211100b5X:?P5O1%0?11=:R?/4A936=R=%0=RK11C6RCA36:7PHPBP>P4O1P1PDb1X3GX0HP5C6X1EX2CP5C6X0=PKe38W4P5O1n200110100021110311100b5X98P5O1%081239,4293;3R2%02R811>;RK12;9,4<P?PAP>P3O1P1PDb1X37X0?P5C6X1@X2KP5C6X02P8e38W4P5O1n200110100021110311100b51@45R8%08'5eX60X70P4P5O2X60X70o"). Qed.
Lemma fvalid_ge8 lo fp : fvalid lo fp -> 0 <= lo -> 8 <= fp.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Chain"] "h01Hh11Dh22H0h32H1h42H2h52H3h67__arithh74__ffh86__sat4h98__varmaph:5__with;4__x1h<4__x2h=4__x3h>2fph?2loh@1qhA1rhB3HlohC2V1hD2V2hE2V3hF6__sat5hG1zp;2p;1p;4p;6p;3p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g00n<j2jTg00<Oj21Tg00jAj1\Tg008oj1=Tg00;7j1MTg00kEj2`Tg00M=j20Tg00M]R6j26Tg00CIj28Tg00Shj2CTg00TYj2Dj3NTg00U:j1iTg00USj25Tg00V0j2;Tg00;Uj27Tg00VMj2JTg00W4j2HTg00W[j2GTg00XAj2FTg00E1j1[Tg00@Lj1ZTg00Xgj1YTg00Eoj1XTg00FMj1WTg00G[j2ETg00\Bj49Tg010:j6VTg00Ifj2STg00JHj2RTg00Jbj2QTg00=Uj3@Tg00KNj3OTg00Kmj4PTg00R@j6TTg010^j2UTg011Oj1hTg011mj2gTg00>nj1?Tg012Nj2<Tg0137j3fTg013`j3>Tg014Ij2dTg0155j2LTg015aj3cTg00EQj2KTg00YEj4ITg00G8j2BTg016Aj1_Tg016fj3aTg00H>j3bTg00IDj1^Tg00\mj7eTg00]Qj8]Tg00`eR0f0R4g00`GR53@p=41854p=2f1R7=@04p=3P7g00ajR2g00bIR3P3g00biR1P4g00cIFep=:f3R8P2P3P3P1f2R9P7P4G]p=A1j74P61197p,2ar#\g00f1R:#=R;#=#=R<#=#M'`R=,17%M<R<,07#4'6%2818<8R>[P4f4R?/1811?=10?<#4'6P6f5R6/1=106<#4f7R6#218<6[P4116=f8/0<#4f:R6#2R=1C6<%2<R?f<R@/0<RA#2[\=f;R=/D<%4<RB#iRC15@<,;<RD/7A,3@[1J@<115<RAf=RE/0<RF#211F<'6[1HE<11<5RFf>RG/0<RH,1<18H5'6[1GG<f?RI/5<RJ#4\B1FI<f@RK/0<RL/3K\B15K<P0fARM/0<RNP0g00gQRO#[RP%ZORQ%Y0RR%X0RS%W0RTP2P3P3P1P01E0<R2g017IRU1E05RVC9,:TEV1ST1R1P4P9g00h=RWg00h]RX'R1Q49=@WXdAO057CPRXb7b9b:g00o]\BP4b6bAb@b5b4b3b2b0b89N6<156<,;<106<'7,36P010=<17D4,3@XG0P4P5P9ET15=<,;</75,3=1C@<%2@%2H\?[1UE<%2E%2J\?[1DG<1;<J10I<'7,3I\C1JI<%2L11L<'6\A1HK<11<N18N5'6\F1GM<fBRM/5<#4\B1FM<fCRF/0</3F\B15F<P0fD/0<P0%h:,g0g00fVRF#?RB#?RN#?RK,<0RA5f01<0FRF5>0%?K,<01<0N9>0A5>01<0B=>0Fg0180'd'L'L=cOPPQP01K09P7P01K08P8PRCICIPSPTP01B0:R:PU%_;,B09a02=b0VC9,:T%^3R3PTP0PVg00ciRV1B0;R;C9,:TP3PTP0P;g00aCP:C9,:TP3P0P2PVP:C9,:TCACACAP1PXb7b9b:X;0X<0X=01;<9/75,34%291189P>[[[^;0^<0^=0P4P9fGfFP6P@PMO6b6bAb@b5b4b3b2b0b8bFb1b1WBWEWDP7P4O2n2001000000121000000W0WCP7P4O2n2001000000121000000W0X>0X?0P7P4O2X>0X?0o"). Qed.

Lemma rchain_frame (M M' : word -> option byte) lo fp RC :
  rchain M lo fp RC -> 16 <= lo -> ar_stack_top ar < 2 ^ 64 ->
  (forall x : word, fp - 16 <= bv_unsigned x < ar_stack_top ar -> M' x = M x) ->
  rchain M' lo fp RC.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Chain"] "p'0h02H0h12H2h22H1h32H3h42H5h52H4h64__x1h74__x2h81xh92IHh:1Hh;4__x3h<7__arithh=6__sat4h>6__sat5h?6__sat6h@1qhA1rhB2H6hC4__ffhD8__varmaphE5__withF4__x4hG1ahH1zi001zhI2RCi012RChJ2fpi022fphK2loi032lohL2H8hM2H7hN2HxhO1li041lhP2AGhQ3HlohR4HtophS3fp0hT3lo0hU2HahV1MhW2M'hX1VhY2V1hZ2V2h[2V3h\6__sat7h]4__x5h^4__x6h_4__x7h`4__x8ha4__x9hb3pc1i053pc1hc1Chd2C1he2C2hf3H10hg3H11hh2H9hi2NVhj3NV'hk1Phl2R1hm2R2hn3RC0ho2V'hp2W1hq2W2hr2W3hs3fp'i063fp'ht4fp'0hu2q0hv2r0hw2rai072rahx3ra0hy1si081si091fi0:1ni0;2z0p%0p%1p&0p;1p;4p;2p;3p;5p;6p;8p;7p;<p;9p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj1=Tg009Tj1{Tg00:2j1rTg00:Uk102Tg00@Lj1zTg018\S00j41Tg00;7j1`Tg00CIj28Tg00jAk10=Tg00<2k205Tg00<Oj20Tg00kEj27Tg00<kj2MTg00=Uj35Tg00n<j2:Tg00U:j1HTg019bj4wTg00=ok10FTg00>nj1DTg00?Mj5ATg00M=j23Tg00E1j1qTg00Cek20:Tg00DMk303Tg00Shj2TTg00TYj2UTg00USj2;Tg00VMj2XTg00W4j2WTg00W[j2PTg00XAj2STg011Ok10MTg011mk20LTg0137j3aTg012Nj2yTg01:hk20KTg01;Qk30JTg014Ij2nTg0155j2xTg015aj3iTg00Xgk10HTg00Eok10GTg00FMk10ETg00G[j2gTg010:k60CTg00IDk10BTg00G8j2vTg016Aj1fTg016fj3eTg01<:j3_Tg00Ifk20@Tg00JHj2hTg00Jbk20?Tg00KNk30>Tg00Kmk40<Tg00;Uj2?Tg00Hak30;Tg01<]j8kTg01=hk709Tg00M]R6j2ETg01>nk204Tg00iaS01k206Tg00R@j8lj6mTg00m=j2oTg01@6m<00Tg01A<m90ATg00V0j2tTg013`j3uTg00EQj2~Tg00YEk40DTg00\Bj4^Tg00\mj7cTg00H>j3}Tg00]Qj8jTg00_cj7|Tg00Q3k60ITf2R0f1R4'8f0R5'Ep=bg00`GR7/801045'Ep=@f3R2/70/84/E5p=9g00`eR3?557p=61004/E5p=>1875p=21t04/?59532p=O1857p=QA5345p=41y35p=JAu3459u30p=I1~35p=VP3P0P4P5H0Dp=<P0g00ajR1g00bIR8P8g00biR9P3P4g017IR:P5C^g00cIR;Fcp=N1v35p=FA}345p=]P2P1P8P8P9P0P4P5Gjp=\P3P4g00aCR<P5C^p=ZP3P4g00ciR=P5C^p=sP0P1P8P8P9P3P4P=P5C^P;Fcp=Yf4R=P1P8P8P9P2P1P8P8P9P0P;FcP4P5Gjp=Gf6R>P1P8P8P9f5R?P=P2P1P8P8P9P0P4P5GjGjp=BP0P1P8P8P9P3P4P<P5C^P;Fcp=K18201045'Ep=RP0P1P8P8P9P4P5F|p=d1045,E0p=pAi345p=CP3P4P:P5C^p>071t04/?5p>08P3P=P2P0P4P5J0Ip=[P?P=1720P4P5DAp=L1874/E5p>01g00f1R:#=R;#=S02#=S03#=R<#=#=R@#{RA#rRBQ03#{#r$02RC[S04Q04%z3RDQ04Q04P=P0P4P5C1P?%`<R</80REp,2ar$0=RF%`;RG%`@RH+05RI'0RJ17=<S051MA5RK10KFRL3bf;RMP4O1f<RNP4O155C[^8BROf:RPP?P=P2C1[[[XIDXJ3XK31:45#HS06PPP?P=P2CwXPOXRJXQEWiXJ3XK31:04S07p,1L$0FREf9ROQ03#`RQ,70S08g00fVRR#DRS#DRT#DRU#DRV#DRW#DS09#D#DRXP4DA%=@#=#=#=#=#=#`R@9@00S0:18<?f7RYP<PKPLC9f>RZP4O1f?R[P4O155C[^8BP?f8R\/:YP610O\17F<R]13\Q#65>\P[PPPO%q3R^C1P510MP13MQ#69>M]P610N]13NQ#6fCR_PZf=R`P^C1P510Z]Ra13[Q#6fFRbfARcf@RdP[PZfGRePb17dQP[20:GHS0;107G%2H107I[[S0<%2GRfg00g5RgB03GH4UWURH%2I\g^UfRffBRg/TQS0=%2g%2QRhfDRi/3QRj#2[[S0>1U_QS0?%6QRk#HRlPiPQ1;iQPjCO[S0@1XiQS0A107QRjfERm/3QRn?@nQ[S0B1WmQS0C10Q7Ro13bQRp%Qp5>Q[S0D1PbQS0E1;eQ#6\kS0F1SeQS0GfHRq/3QRr/4q\kS0H1;qQS0IP3fIRs/3QS0JP3P6%2sRt10s@RufKRv/7QRw#2Pb%2vS0KfLRx/0@Ryg00gQS0L&0M:-0L3S0M%JVS0N5a3Q0M%JURU5a3S0O1y3RRR3I20K3Q>0J3RS0P%JWS0QQ0N%JTRT7IU3Ig0180S0R'n'xQ0L#qS0S3iS0TQ0L#zS0U&0H3RU%V=7<=S0V%V2S0W?<0U7<4&0G3S0X&0E3RWPWPWP1P8P8P91g3QR11g37RV5NWJ0CS0Y&0B8R81v3:Rz%f:R:#=#FS0Z9e31%f;S0[#FS0\']5NWC\P8PWQ0\=NWVP8PWPW%F:R{/ZzP8PWPW1g3<R|/s{P8A_3z1R}9YWVS0]DGDGFB20@W9S0^P5P0g00h=R9g00h]R~'h20?50=59~dB0>374H0<S0_bCbDbEX63X73X;3XF3g00o]\kS0`P4PQP=P2CO[S0a%62S0b1020S0c18<=S0d17=QS0e#2[[[[^63^73^;3^F3S0fP5P>P?fPR7fOR~PMP[PifJR9O8b<W4W5P4P5O2n2001000000121000000bAb@b3b1b2b0b:b=b>b?Q0;Q0<PHPfQ0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IP3Q0JP3P6PtPu1?wQ/0IPbQ0KQ0L%JSS0I=ITRQ0R'nQ0S3iS0HQ0U%V0RT?<0US0G?<4UQ0XPWPWQ02#FRR=_3|,ZzP8PWPW1g3G>0;3AS0F,ZRP81]}1RGQ0F5KWS0EDGDGQ0^Q0_bCbDbEX63X73174<,05S0D100IS0CQ08/?Q/0I[[^63^73S0BP5PFP~PdPsO4b<X4yW5P4P5O2n2001000000121000000bAb@b3b1b2b0b:b=b>b?17cQRyPKPK1?yQCRPMP4Q0;Q0<PHPf1TiQ%2iS0A%2p\h[1UmQPbPQ1;bQPpCO\l1XbQ13eQRp?@pQ\j1WeQ%Qr9>Qr\o1PqQ1;sQ#6\k1SsQ139QRr/49\k1;9QRpP313vQRyP3P6Q0K10v@fMRSP<1MANS0@Q0@/0FS0?C9Pq%2SfNRw/0@Q0HQ0UQ0W9<T4S0>Q0XPW%F;R;9YW}AKW;G5dWP8PWPWA_3{|,ZzP8A_3z|S0==YW;S0gAKW;{S0h5dWS0iDGS0jC\Q0^Q0_bCbDbEX63X73X;3S0k175QR{P4P41?{QCR172<,04170<S0l102=S0m7b2[S0n[^63^73^;3S0oP5PF1MAdfQR{P[PgO5b<W4W5P4P5O2n2001000000121000000bAb@b3b1b2b0b:b=b>b?O2WNX8BP`GkPNK09W[WZP4P5O2n2001000000121000000W:WYP4P5O2n2001000000121000000b:WPXRJWQWkWcWXXb3XJ3XK31:=2S0pPEPMQ0ePXP2DAP@P=P=PICRS0qPEP`17><S0rPXP=DA%2?S0s?p?IS0tP[P\P>P?C118<OPPP<PKPLC9P_P4O1PiP4O1RG55C[^8BPgPNPPPOC1[\J[18<MS0uP`P<PKPLC9PmP4O1S0v95CG[^8BPO1:Z`P610[Z13ZQ#6,EaPmPdP[1CZNC1P510cd13cQ#69>c]P610g]13gQ#6PsPiP_1CgdC1P510i]%6nPxPePbPmPiP_PgPSPx17bQPmQ0;Q0<PHPf1TqQS0w%2q%2r\h[S0x1UsQS0yP9PQPpPrCO\lS0z1X9QS0{A@yyQ\jS0|1WvQS0}13xQS0~Q0~#Q5>Q\oS101PxQS111;SQS12#6\kS131SSQS1413wQRy/4w\kS151;wQS16P313~QRrP3P6%2wS1710wIS1817{QS19#2Pq%27Rp10{IS1:fTRn,8<S1;PvP5PsO2WGS1<Q1;PnP<PKPLC9f]RaP4O1f^RGP4O155C[^8Bf\R}fVRuPnfSRtC1[]GS1=Q0TQ0UQ0W9<T=Q0V7<4S0VQ0XPWPWQ0YP8%f:#FS0W9e31Q0Z']9NWzC\S1>P8PWQ0Z=NWVS1?P8PWAKWRzS1@P8PWAYW|RS1AP8Q0]FBFBQ0^Q0_bCbDbEX63X73X;3XF3Q0fP5PYP>fWRRPuPNPdPmPvO8S0fb<b9WBW4P4P5O2n2001000000121000000bAb@b5b3b1b2b0b=b>b?Q0;Q0<PHPfQ0wQ0xQ0yQ0zQ0{Q0|Q0}Q10Q11Q13Q14Q15Q16P3PrP3P6Q17Q18Q19/?Q/0IPqQ1:Q1<Q1=Q0HQ0UQ0G9<U4S0GQ0XPWQ0\=_3|S199KWzS0]P8PWQ0\Q0F5KWS1BP8Q0EFBQ0^Q0_bCbDbEX63X73Q0BP5PFPuPcP9O4S0Bb<b9WBX4pP4P5O2n2001000000121000000bAb@b5b3b1b2b0b=b>b?17eQR:PKPK1?:QCRPMP4Q0;Q0<PHPf1T9QS0E%29Q0~#2\h[S1C1UvQS1DPxPQ1;xQQ0~CO\lS1E1XxQS1F13SQS1G#2S1HQ1G;pQ\jS1I1WSQS1J%Qy9>Qy\oS1K1PwQS1L1;~Q#6\kS1M1S~QS1N137QS1O/47\kS1P1;7QS1QP313{QS1RP3P6Pp107IS1SPtP<Q0@Q0?C9S0?P9fRS0@#2S1T10tIS1U18<uS1VPSP5PvO2WGS1WQ1VPuP<PKPLC9f_R:P4O1f`S1XP4O1S1Y55C[^8BPGfXRTPufUS1ZC1S1[[]GS1VQ0kQ0oP5PF1MAcPTPdP_O5S0ob<b9WBW4P4P5O2n2001000000121000000bAb@b5b3b1b2b0b=b>b?O2WNX8BPcGkPdPSPx17b<PiQ0;Q0<PHPfQ0wQ0xQ0yQ0zQ0{Q0|Q0}Q10Q11Q13Q14Q15Q16P3PrP3P6Q17Q1817{<S0k#2PqQ1:Q1<Q1=Q0TQ0UQ0VQ0XPWQ1>P8PWQ1?P8PWQ1@P8PWQ1AP8Q0=9YWVFBFBQ0^Q0_bCbDbEX63X73X;3XF3Q0aQ0bQ0cQ0dQ05#2[[[[^63^73^;3^F3Q0fb<b9WBX4pP4P5O2n2001000000121000000bAb@b5b3b1b2b0b=b>b?Q0;Q0<PHPfQ0wQ0xQ0yQ0zQ0{Q0|Q0}Q10Q11Q13Q14Q15Q16P3PrP3P6Q17Q18Q0k/?Q/0IPqQ1:Q1<Q1=Q0HQ0UQ0GQ0XPWQ0]P8PWQ1BP8Q0=/]1S0=Q0F5KWFBQ0^Q0_bCbDbEX63X73Q0DQ0CQ0l/?Q/0I[[^63^73Q0Bb<b9WBX4pP4P5O2n2001000000121000000bAb@b5b3b1b2b0b=b>b?17e<S0BPKPKQ0B/?QCRPMP4Q0;Q0<PHPfQ0EQ1CQ1DQ1EQ1FQ1IQ1JQ1KQ1LQ1MQ1NQ1PQ1QP3Q1RP3P6PpQ1SQ0?P9Q1TQ1UQ1WQ1VQ0HQ0UQ0>Q0XPWQ0gQ0=9KW;5dWP8Q0jC\Q0^Q0_bCbDbEX63X73X;3175<RpP4P41?pQCRQ0n[^63^73^;3Q0ob<b9WBW4P4P5O2n2001000000121000000bAb@b5b3b1b2b0b=b>b?O2WNX8BP[GkPZ204bi1:biRp%Hp+06Q011:emRp%HpPwPqPbPmC1P51:qbS01P[Q0;Q0<PHPf1TvQQ0KQ1H\h[1UxQPSPQQ12Q1GCO\l1XSQA@yyQ\j1WwQ%Qr9>Qr\o1P~QQ1Q#6\k1S7QQ1R/4{\k1;{QP3Q0@/3QP3P6%2{S1RQ1:Q1;Pv%2t10nI18<RRrPwP5PxO2WGPRP<PKPLC9Q1YfaRyP4O155C[^8BP:fYRpPRPuC1S1Y[^GrQ0TQ0UQ0VQ0XPWQ1>P8PWQ1?P8PWQ1@P8PWQ1AP8AYW|zFBFBQ0^Q0_bCbDbEX63X73X;3XF3Q0aQ0bQ0cQ0dQ0d[[[[^63^73^;3^F3P5PYP>fZRrPpPNP_PqPwO8b<b9WBW4P4P5O2n2001000000121000000bAb@b5b3b1b2b0b=b>b?P`PqP<PKPLC9PZP4P610vsQ0J#69>s]PxP<1MA0S0JQ0J/0FC9P010SvQ0~#69>x]P610S]Q1G#6P7P<1MA>S1GQ1G/0FC9P510~]Q1O#61T{QQ1R13tQ#2\h[Q0;Q0<PHPf1TuQ%2u13TQRf#2\h[1URQPTPQ1;TQPfCO\l1XTQ13pQRf?@fQ\j1WpQ13rQRf%Qf5>Q\o1PrQf[Rf/;Q#6\k1SfQ13}Q/4}\k1;}QP313aQRHP31U}QPaPQ1;aQPHCO\l1XaQ13GQRl?@lQ\j1WGQ13:QRj%Qj5>Q\o1P:QQ1X/;Q#6\kQ1X/SQ13yQ/4y\k1;yQP3fbRk/3QP3P6fcR6#2106IffRoP<1MAxRj10jFC9PafeRj#210oIQ0vQ0s\hfjRh,8<S0sPyP5P:O2WGQ0s17h<S0v?bKLfsRlP4O1ftS0<P4O155C[^8BfrS0;flRHPhfiR]C1[]GQ0L%DXS0s#JS1RQ0M%JXS1O5a3Q0QQ0NQ0O3I3IQ0PQ0MQ0s#D#J5a3Q1RQ1OQ0MQ09#J5a3Q0NQ0I3I3I3IQ0R'n'xQ0S3iQ0U%VY?<OU%VO?<?U7<0%V\?<=U%V>7<27<4Q0XPWPWQ0YP8Q0\Q0[#=#F9e31Q03#FRU']5NWC\P8PWPWQ0YP8Q02#f#F9e31Q0W']9NWzC\P8PWQ19=YW;Q0h5dWP8PWANWUVP8PWPWQ0\,ZzP8PWPWQ0W007VP8PWPWQ0Z/ZzP8PWPWQ0Z,s|P8Q0iDGDGDGDGFBFBQ0^Q0_bCbDbEX63X73X;3XF3X]3X^3X_3X`3Xa3Q0`B08QOYR8,4=[Q0`1408[P?P<P2Q0mC9%6O10=Y%6P10P>Q0uP\P<PO10OPC9[[[[[[[[^63^73^;3^F3^]3^^3^_3^`3^a3P5P\P[PYPZfmR8PhPFQ0@,MAPHP`PiP{PsPwPuPfPyOAb<b9b\WgWfP4P5O2n2001000000121000000bvbubhbLbMbBb4bAb@b5b3b1b2b0b=b>b?b\WrWqP4P5O2n2001000000121000000W0WpP4P5O2n2001000000121000000O2WNX8BO3WoP5O1Q01#HQ00P7142S142xA5D2xPuP7PwPSC1[[[PdQ06140~140wA5D^wQ0@,4?P514>tPn14YtRwA5D^tRt1:0O#HQ1[]0]3]1XH3Q0@,4>P5PwPnA5D^nRw1:T4#HQ1Y]0]3XH3P5PwPDP^1:pR#HQ1XPrPTP4C1]0XOD1:Tu#HPDP^PyPrPTP5C118<fP}P<PKPLC9PjP4O1R{PoP4O155C[^8BfdRAPGP}P=C1[\J[PkP}PrP^C1]9]:XIDQ1XPpPRP^C118<rPfP<PKPLC9PAP4O1=5C{[^8BP6PaPfP^C1[\J[PyPfPpPgCwW9W:PuP0P7P~GlW0Q1ZP5Emb0X3tP\P5D[b0W1PYP5D[b0W2P0P4P5P2O4W3W1W2W0XS3XT3P0P4P5O3Q07PEPrQ08PXP4DAQ0:Q1Z,4?14?n14\TP514OpPr14PpRnA5D^pRp1:0NPEPjP`PQPXPNELA@``@PoQ1XPGPaC1]1]2]0]4]5XH314OTP5PnPrA5D^rRr1:G4PEPoQ08PXP`DAA@ZZ@RnfgRNPyP:PGC1]1]2]0]4XH3P5PrPDP^1::aPEPNPGPQPXPZELA@[[@fhRrPkQ1XP2C1]1]2]0XOD1:G}PEPoPaPQPXP`ELPDP^P]PkQ1XP5C118<6PAP<PKPLC9P8P4O1RafnR}P4O155C[^8BPHPoPAP=C1[\J[PhPAPkP^C1]9]:XIDPrPyP:P^C118<kP6P<PKPLC9PHP4O1=5Ca[^8BfkRaPjP6P^C1[\J[P]P6PyP^C1P9P=O1'oW9W:PGP=PTPRGlX1nW2W0PfP5Emb0X4pPMP5D[b0W5PPP5D[b0W3P0P4P5P?P=P2O6X4wW5W3W1W2W0Xb3XS3XT3P?P=P2P0P4P5O6Q0pPEPyQ0ePXP2DAQ0qPEP6Q0rPXP=DAQ0tPjP\P>P?C114P:14PG1CP\=5DG14`kP514Z6PA14[6RG1C[`=5D6R61:0cPEfoR`PgPQPXPcELP@PgPgPICRPEfqR:PiP<PXPgEL10_IRy-01_PlPbPiP_C1PlP8PaPhC1]4]5]3]1]2]0]L]MXH314ZkP5PGPA1CdZ=5DARZ1:r4PEfpRGQ08PXPgDAAb@_yRyPEQ0;Q05PXP_DAQ0A10iIRk'ERhQ0<P>PmPiC1Q0<P}PHPaC1]4]5]3]1]2]0]LXH3P5PZPD1Cc[1:]NPEP:PrPQPXP_ELAb@ikPEPlQ0vPXPiDAA@mmIfuRIPHPbPmC1PIP`P8P>C1]4]5]3]1]2]0XOD1:roPEPGPNPQPXPgELPEQ0;P]P<PXP_ELQ0<PaPmPiC1PD1CemRmfvRiP`P8P5C118<GP:P<PKPLC9fzP4O1R8f{P4O155C[^8BfyR_PlP:P=C1[\J[fwP:P`1C9qC1]9]:XIDPIP}PHPmC118<`PGP<PKPLC9P_P4O1=5C8[^8BfxQ0;PG1CvsC1[\J[PiPGP}1CseC1PRPYO1'oW9W:PaPYPjPAGlW4X5hW3X1yW2W0PjP5Emb0XL6PdP5D[b0WMP[P5D[b0WBP0P4P5P\PYP>P?P=P2O9WLWMWBW4W5W3W1W2W0XnDXt3Xx3XS3XT3PPPOP\PYP>P?P=P2P0P4P5O;n10410010;10400000033110310200061103102105000000000;1103102107106101000000000000000000140x140vA5D0vQ1ZP~PSPxC1[[[XODXH3XH3PsPePbO3P51h391h3q1hDeO3b0WjP5O1n20011080002111091110:byN<00W[WZP4P5O2n2001000000121000000W0WYP4P5O2n2001000000121000000b0WPXRJWQW9W:WmWeWlWdWXXIDXs3Xw3XJ3XK3P2P0P4P5N90AW:XIDXJ3XK3WWWVP=P2P0P4P5O5WIXJ3XK3WWWVo"). Qed.

(* [comment removed for export] *)
Lemma rchain_frame_sp (M M' : word -> option byte) lo fp RC :
  rchain M lo fp RC -> 16 <= lo -> lo mod 8 = 0 -> fp <> lo + 8 -> ar_stack_top ar < 2 ^ 64 ->
  (forall x : word, lo <= bv_unsigned x < ar_stack_top ar -> M' x = M x) ->
  rchain M' lo fp RC.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Chain"] "p'0h02H0h12H2h22H1h32H3h42H5h52H4h61zi001zh71Hh82H8h92H7h:2H6h;2RCi012RCh<1li021lh=2H9h>7__sat10h?7__sat11h@7__sat12hA6__sat9hB3fp0hC3lo0hD1qhE2q0hF1rhG2r0hH2D1hI2D2hJ2HahK1MhL2M'hM7__arithhN4__ffhO7__sat13hP8__varmaphQ5__withR4__x1hS4__x2hT4__x3hU4__x4hV4__x5hW4__x6hX2fpi032fphY2loi042lohZ1xh[2AGh\3Hloh]4Hlo8h^3Hneh_4Htoph`2Hxha3NV'hb3RC0hc2V'hd2W1he2W2hf2W3hg7__sat14hh3fp'i053fp'hi3pc1i063pc1hj2rai072rahk1si081si091fi0:1ni0;2z0p%0p&0p;1p;4p;2p;3p;6p;9p;7p;5p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj19Tg009Tj1qTg00:2j1jTg00:Uj1wTg00@Lj1rTg018\S00j40Tg00;7j1STg00CIj2CTg00M=j21Tg00U:j1>Tg00jAj1sTg00<2k20BTg00<Oj22Tg00<kj2ZTg00=Uj37Tg01>nk209Tg00n<j26Tg00iaR6k205Tg00kEj2RTg00Shj2HTg00Cek200Tg00DMj3~Tg00TYj2Mj3nTg00USj25Tg00V0j2WTg00VMj2NTg00W4j2PTg00W[j2FTg00XAj2KTg00E1j1fTg00Xgk10ATg00Eok10@Tg00FMk10?Tg00G[j2eTg00Ifk20>Tg00JHj2YTg00Jbk20<Tg00KNk30;Tg00Kmk40:Tg010^j2bTg00R@j6Tj7\Tg011Ok108Tg011mk207Tg00>nj1BTg0137k306Tg01:hk204Tg012Nj2mTg01;Qk303Tg014Ij2lTg0155j2dTg015aj3cTg00EQj2`Tg00YEj4UTg00G8j2ETg016fj3kTg00H>j3_Tg00IDk102Tg016Aj1^Tg01<:k301Tg00\Bj4VTg01BDl9{Tg019bj4|Tg00=oj1zTg00?Mj5XTg00m=j2hTg00;Uj2aTg00M]R0j2QTg00\mj7yTg010:j6xTg013`j3vTg00_cj7uTg00]Qk80=Tg00Q3j6tTg00`eR4f0R5g00`GR737p=:f2R2f1R3/a5574p=L1C23/Q5p=<1223/Q5p=@1C75p=41235,Q2p=p1C57p=GA7435p=3f3R11W23/a5574p=A1C721235'Qp==P4P3g017IP5CVp=[P3g00ajR8g00bIR9P9g00biR:P5g00cIFyp=?P3P8P9P9P:P5Exp=o1m45p=IAv435p=;P4P3g00ciP5CVp=]P2P8P9P9P:P3P5Fup=iP1P8P9P9P:P2P3P5L0=p=J1W23/a5p=}P4f4R8P1P2P3P5Etp=Of5R;P81R12P3P5DXp=8Ac435p=D1C73/Q5p=gg00f1R<#9R=#9#9R>#9R?#9#9R@#qRA#jRB%q>#j#wRC[RD%r4REP8P2P3P5C0%S?R?/C1%S>RF,18#:AL8;F#>p,2ar#sRG%S=RH%S@RI+0BRJ'2f8RK1ZA5RL12LGRM3<f:RNP3O1f;ROP3O157C[^ZBf7RC-09K16KCRP%>P+05P6f9R6/6KRP%>PPOPNP6PKC0P516N6S01f=RPf<RQPOPNP6PKPCP81RO??<LMP;P3P012PQ1RG?RM11QF#:5@Qf>RL1ZA2RR12RG3<P2f?RR/2L11RF#:9@RMP0f@R0/2M110F#:fBRSf6RT,ZARU12UG3<P512SMfCRM/1F#:fDRUfERV/HF%4VS02%4FRWfGRX/1F#4[[200HIS03127H%4I127J[[RY%4HRZg00g5R[A~HI3UWJRI%4J\[^JZRZ1HXF%4XfIR[/1FRH#4\W[fHR\/MF%:FR]#>R^15[F,WFR_=L[H[1N[F127FRHfJR`/1FRa#4Rb?paF[1P`F12F7RafKRc/1FRd%Gd5@F[1FcFfLRe/5FRf#:\]1KeFfMRg/1FRh/3g\]15gFP4fNRi/1FRjP4fPRk/MFfQRlPF15lF11lFRmCA\^1NlFfRRn/1FRo?=oF\H1PnFfSRo/1FRp%Gp5@F\a1FoFfTRq/5F#:\]1KqFfURr/1FRs/3r\]15rFP4fVRt/1FP4g00gQRu#fS04%ruS05&0A4S06&0@4S07&0?4Rv1e4FRw1e47Rx'[,?v'o20>v:S08P5P2g00h=R:g00h]Ry'Y20<52=7:ydB0;473H0:S09bNbPbQg00o]S0:\]P5bMRybGbEb=b8b9b:b4bFbDb5b3b1b2b0bAb>b?b@7nFPUPF15UF11UFCAfFR:1H:F%4:11\FS0;#4\W[Q03PYPIPZ1H\F%4\Pb\W[1b[F%4[Rb15cFRz#4\W[1M`FPcPFPzPdCA\^1NcF11eFRz?=zF\H1PeF%Gh9@Fh\a1FgF15iF#:\]1KiFfORh/1FS0</3h\]15hFRzP411kFR{P41MnFPoPF15oFS0=PpCA\^1NoF11qFR|?=|F\H1PqF%Gs9@Fs\a1FrF15tF#:\]1KtFfWRs/1FS0>/3s\]15sFS0?P4fXR}/1FR~P4PybGbEb=b8b9b:b4bFbDb5b3b1b2b0bAb>b?b@bO7nF15:F,WFRy11:FS0@5L:P4Q0@PXPF15XFP5CAX64P3P7P2ETAL:y7P4Q0;AL[_5X64P3P7PMETP\PF15\FP7CA1H[F%4d\W\b1b`F%4`%4f\W[Q03PYPIPZ1HeF%4e%4j\W[1bgF%4g%4z\W[1MiFPhPFPzQ0<CA\^1NhFA={{F\H1PkF%Gm9@Fm\a1FlF15nF#:\]1KnF13po\]Q0=P4P|P41MtFPsPFQ0?Q0>CA\^1NsFA=~~F\H1P}FfYRH/1FR~%G~5@F\a1FHFfZRa/5F#:\]1KaFf[R~/1F/3~\]15~FP4f\R]/1FP4&08<-074g00fVR^#BR|#BRp#BRm#B#B#BR{#BRz#I6064RW%I{R{%Ip';';2044F1m4^R^6034%BzRz#IRp%I|R|,;{,;W';';g0180Rj'l'd%ImRm,;{,;W1;Wm,;p1;|^/lj'd'dQ045cu5cuQ05P4P4P41`4TPTQ06CUP2Q06CUP3P41`48P11`4;CUCUQ07Pv1E4<Ru1E4>9k4w=_4x'[,?v&029R9Pv%^=,E4R>%^<R<#^,E49k4w=_4x'[,?vP9Pv1e4?Rx:014>1E4=R='],?vP4P=g00aCRj1E4<CV,?vR<5ivP9PvP4PuPjP>CV,?vP9PvA_4uw,[>,?v,ovP9Pv1]xu,?vP91]u=,?v=iv<CJCJCJCJCJCJQ08Q09bNbPbQXR4XS4XT4XU4XV4XW4A}F;7R7,3513871R;?12187<1121TALC8FQ0:[1C?;12CK9<TC[[[[[[^R4^S4^T4^U4^V4^W4P5P2P6f]R7PG1ZAnf^RAPVP:PlPiP}PaO<bMbGbEb=b8b9b:b4bFbDb5b3b1b2b0bAb>b?b@bObgbIbHbIbHWfWeP3P5O2n2001000000121000000W0WdP3P5O2n2001000000121000000O2W`XZBM9{WcP5O1Q01#>Q00PP131RRBA7E1RPMPSfARGP0C0[\B[PK1635#>132GRB%f4R<=7EG13;UP513TVRvP:13C:R=A7E<:Ru1626#>PcP`P[P\C0]0]3]1X64P5P=PXA7E<XR=16`3#>PePcP`P[C0]0]3X64P5P=PEP<16c`#>PgPePcP3C0]0X<E16`[#>PEP<PiPePcP5C0PiPgPeP<C0]7X;EPgPcP`P<C0PgPePcPGC|W7P[P2P\F\W0P\P5ETb0X3uPKP5DOb0X1vPCP5DOb0W2P2P3P5P1O4W3X1BW2W0XB4XC4P2P3P5O31623p,1L#zRBPX1R2FRvPzP3DX%9@#9#9#9#9#9#SR@9=2213;XRu13K`P5136cRcPe13NeR`A7E<eRe162QPBPnPPPFPzPQE8A=PP@PoPnPlPkC0]1]2]0]4]5X64P5P`PgA7E<gRg16k3PBPoPvPzPPDXA=LL@R`PqPoPnPlC0]1]2]0]4X64P5PgPEP<16lkPBPqPlPFPzPLE8A=RR@PrPqPoP1C0]1]2]0X<E16khPBPoPkPFPzPPE8PEP<PtPqPoP5C0PtPrPqP<C0]7X;EPrPoPnP<C0PrPqPoP<C0P[P1O1'hW7PlP8PkF\X1`W2W0PiP5ETb0X4ePOP5DOb0X5cPNP5DOb0W3P2P3P5P;P8P1O6X4=X5uW3W1W2W0Xi4XB4XC4P;P8P1P2P3P5O61681PBPiP8PFPzP1E8128J9<@8PBPkPTP?PzP8E8A=;;JPnPKPTP;C013NlRn1DNK=7El13PqP513LrRrPt13RtRq1DRP=7EtRP162GPBP]PSPFPzPGE812SJ9<@SPBPAPUP?PzPSE812MJRl,gMf`RkP:PUPMC0Pkf_RiPAP7C0]4]5]3]1]2]0]8]9X64P5PqPs1D0L=7EsRs16a3PBP7PvPzPSDXA<@MlRlPBPiP8P?PzPME812UJRv,gURqfaRuPTPVPUC0PuPkPiPAC0]4]5]3]1]2]0]8X64P5PsPE1DGR16~aPBPAP~PFPzPME8A<@UvPBPkP7P?PzPUE8Q02?pVJfbRJPiP:PVC0PJPuPkPTC0]4]5]3]1]2]0X<E16aHPBP7PaPFPzPSE8PBPiP]P?PzPME8PuPAPVPUC0PE1DXVRVfcRUPuPkP5C0PUPJPu1D[XC0]7X;EPJPkPiPVC0PJPuPk1D\:C0PtPTO1'hW7PAPCP7F\W4X5qW3X1lW2W0P}P5ETb0X8PP0P5DOb0X9rPRP5DOb0W:P2P3P5PKPCPTP;P8P1O9W8X9nW:W4W5W3W1W2W0XbEXh4Xj4XB4XC4PNP6PKPCPTP;P8P1P2P3P5O;n10410010;10200000033010410300061104103106000000000;1104103107105101000000000000000000132LR;A7E2LPSPGP0PRC0[\;[X<EX64X64POPNP6O3P51Y4Q1Y4O1YENO3b0WaP5O1n20011080002111091110:bkW[W_W^W]W\W7X;EXX4XY4XLDXKDP8P1P2P3P5O5W;XX4XY4XLDWKo"). Qed.

(* [comment removed for export] *)
Lemma rchain_total (M : word -> option byte) :
  (forall a, 0 <= a -> a + 8 <= ar_stack_top ar -> exists v, 0 <= v < 2 ^ 64 /\ cell_is (hl_segs L) M a 8 v) ->
  forall (k : nat) lo fp, 16 <= lo -> ar_stack_top ar - fp <= Z.of_nat k -> exists RC, rchain M lo fp RC.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Chain"] "p'0h02RCh14__x1h21Hh34__x2h42H0h52H1h62H2h72H3h87__arithh94__ffh:6__sat4h;8__varmaph<5__with=1qh>1rh?3Hk0h@4__x3hA4__x4hB4cstrhC2H4hD2H5hE6__sat5hF6__sat6hG1vhH1xi001xhI2H6hJ2H7hK2HkhL2fphM1khN2lohO1si011shP2H8hQ2HahR3HlohS1MhT2V1hU2V2hV2V3hW4__p1hX6__sat7hY4__x5hZ4__x6h[4__x7h\4__x8h]4__x9h^1eh_3Cfph`3Craha3H10hb3H11hc3H12hd2H9he2Hihf2IHhg2Lohh2NVhi3NV'hj2RDhk3Rfphl3Rrahm1Vhn2V'ho2W1hp2W2hq2W3hr1Xhs1aht3fp'hu2q0hv2r0hw2rahx1yhy1zi021fi031li041np%0p&0p;1p;2p;5p;4p;6p;3p;7p;<p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj1;Tg009Tk101Tg00:2j1{Tg00:Uk10>Tg00;7j1\Tg00;Uj2>Tg00jAk10OTg00CIR6j23Tg00<2k20BTg00=ok109Tg00>nR0j19Tg00?Mk502Tg00M]R4j2<Tg01CNS00j2:Tg00kEj27Tg00BiR5j14Tg00@Lk100Tg018\j46Tg00E1j1~Tg00n<j2UTg00<Oj20Tg00N^k10HTg00JHj2mTg00SAj4`Tg00Shj2STg00M=j22Tg00TYj2TTg00U:j1ATg00USj25Tg00VMj2RTg00W4j2[Tg00W[j2ZTg00XAj2XTg00Eok10WTg00FMk10VTg016Aj1lTg00G[j2]Tg00IDk10UTg01Chk60TTg00Ifk20STg00Jbk20RTg00=Uj3dTg00KNk30QTg00Kmk40PTg019bj4qTg01DLj4bTg01>nj2|Tg00iaR7j2oTg01Dfj1_Tg011Ok10NTg011mk20MTg0137j3iTg012Nj2yTg01:hk20JTg01;Qk30ITg014Ij2xTg0155j2wTg015aj3pTg00Xgk10GTg00G8j2tTg016fj3^Tg00i=k20?Tg00Cek20=Tg00DMk30<Tg01=hk70;Tg01EKk10@Tg01EiR2k10:Tg00R@k60CTg00Hak308Tg01@6m<0ETg01FMk40FTg00^Xl<rTg00R\m<07Tg00V0j2zTg00EQk206Tg00YEk40KTg01<:k30LTg00\Bj4fTg00\mj7cTg00]Qj8gTg013`j3}Tg010:k605Tg00H>k304Tg00_ck703Tg00`GR3f0R1'3p=1f2R8f1R9/01'<p=ng00`eR:1291;d3p=H1089/<1p=?1313p=E1m:1p=Bg00eRR;P:P:P:P5P5f3R<P8P9g00fVR=P3P1M<rp>0AP:P:P6f7R>P6f6R6f5R?f4R@P<P8P9P1N<07p=aAd:13p==1z89/>19d:<p=M13381091'<p=CAd:91p=I206:1p=YP:P8P9P1H0Kp=81t:1p=FB0L:91p=WP:P9g00ciRAP1Cfp=eP:P9g00aCP1Cfp=VP@g00ajRBg00bIRCPCg00biRDP<PBPCPCPDP8g00cIREFcP9P1Ggp=LP;P;P:P:P0P5P5P<P2P8P9P1M<rp=kP;P:P:P:P5P5P?P@P<P8P9P1M<rp=j1y:1p=GA}:919}:8p=NP8PBPCPCPDP:P9g017IR5P1CfPEFcp=vP9PBPCPCPDP1J05p=sB04:91p=JP:P9P5P1Cfp=OP@PBPCPCPDP<P8P9PBPCPCPDP1PEFcGgp=QP9PBPCPCPDP1PEFcp=hP8PBPCPCPDP:P9PAP1CfPEFcp=PP6PBPCPCPDP?P@P<PBPCPCPDP8P9P1GgGgp=DP?P@17<8P9P1I02p=@P8PBPCPCPDP9P1K03p=u1789/31p=K1z89/>1p>0Dg00f1RE#;S01#;S02#;RA#;R5#;#;R2$01S03#{&01A#{$0>[S04Q04%11R0%\ARF,>9p,2ar$0ORG'3Q01#\RH%\2RI+0BRJ9n01R0p,1L$09RKP@P<%9=S05#9RL#9RM#9RN#9RO#9S06#9S07#9RPP1I02'<XG:,::[[^s:%\5R5/39S0817G9RQ%4<'3&00:RRf8RSP@P<P1C6X0R':[[^L:^N:S09XM;Q08%4=RT,3QPRP>P@P<P1C6X0R%~:S0:P6P<P81U<8RUP410@<17G5RV1H<F5?<g00o]S0;P1106?1H6F9?6VRWP410>V1H>FQ0;P1f9RX/0VRYf:RZ/HFR[f;R\,7GR]/3T%E]R^P1XH:R_1391$0HXx:XH:S0<P]P]%B]PTP_P3O1P_P_%41#BXH;S0=1m:3H0AGaPXC`P^f<R^/SF%1^%1FRTf>R]/2FR`#1[[f=S0>/TF%=FRa#ARbP]PF15]FP`CM[1R]F103FR`f?S0?/2FS0@Q0@;CF[Q0?/[F10F3Rcf@Rd/2FRe%Ee5?F[1ZdFfARe/5F#=\a1XeFfBRf/2FRg/If\a15fFRhP:fCRi/2FRjP:p-0Rkg00gQS0A#~RlQ0A$00Rm%Y9S0B%Y8Rn788&0W:Ro&0V:RpPp%lERq#FS0CQ01#FRr'W1]:3Rs'e&0UCRtPpPpQ0C1]:5Ru'W,VrPtPpPBPCPCPDP@J0TDLDL20SpDRDP1P8g00h=RCg00h]RB'm20R18=dCBdB0Q:39H0PRBb9b;b<X1:X3:WW1791#E1785,09P@[[^1:^3:^WkP1Q0;PGfERkPXP\O5b8b>b=b7b6b5b4b2b:b?WVWUP9P1O2n2001000000121000000W2WTP9P1O2n2001000000121000000W2%AURCeCqCbWKWRXL:XN:Q09Q08%9@#4,3Q1|<81oUCP71U@<RC%ACP\P6P?P1C6X0R,:RP11U?@S0DP11U6?P410>6PWP]PXPSP1C6X0R,:RP110XS1HXF,<YP410ZVP[PfQ0>P^P1C6X0R,:RP110^VS0EQ0>/HFPi17]F17G]R[%9eRY#4RW'3%4eRC%\ERU'>,3[RQP_Q0<P[P[%B[PWP_1>1UXH:RWPCO1R[O1P_P_Q0=PYP[PWPePC%BCCkEjGaP^C`S0FPQ%_fS0G%4f#1S0H1SdFS0I%1d%1g\T[S0J1TeFS0KPfPFPhPgCM\bRg1RfFRhACjjF\`Rj1[iFRCfDR[/2FS0LQ0L#E5?F\cRY1Z[FRv15kF#=\aRw1XkFRxfFRy/2F/Iy\aRz15yFR{P:fGS0M/2FR|P:Q0A&0NE-0M:R}%GNRN5i:S0N%GMS0O9i:}1y:=R=3N20J:F>0I:=S0P%GOS0QQ0O%GL5NN3Ng0180S0R'x'w;plS0SPm%Y<RN%Y@S0T788&0G:RL789PoPpPp1]:FRO=vps,spS0UPtPp1t:ERE%;q#FS0V9^:OQ02#FR='J'ODQPtPpAvp=sS0WPtPp1VrE,hpS0XPtPpAPpurS0YPt1WEORM9PpsFDFDPDPBb9b;b<X1:X3:X@:XA:Q0;\aS0ZP9PFP@P<CM[S0[%=<S0\10<8S0]135@S0^17@F#1[[[[^1:^3:^@:^A:P1P8P9fJR~fIS0_P>P\PdfHS0`O8b8b>b=b7b6b5b4b2b:bBb?Q0FPQQ0GQ0HQ0IQ0JQ0KPgPhPjPCPYPvPwPxPzP{P:P|P:PlPmA8n9LS0KPoPp1Wru,VE,hpS0JPtPp1JMO/erDQPDPBb9b;b<X1:X3:1795S0I,01S0H179F/>F/38[^1:^3:P1PGQ0_P^O3b8b>b=b7b6b5b4b2b:bBb?O3PKPkQ0?PFPPP1E@,<0XG:,::Q00P:PKPyPdPFPPP1E@,<0XG:Q0MPfPeP1C6X0R,:RP1PKQ0`PfPFPPP1E@,<0P4%19RM109JS0G'<S0FPKQ0_PiPFPPP9E@fKRiPyPkP1C6X0R,:RP1AC<<JS0aPKfLS0bPyPFPPP@E@%;2#;#;#;#;#;#\R2-0??10?2Rn%An'oP71062Rn%AnfPRnPiP~P1C6X0R,:RP110>2R|PRfQR{Q0bPiP1C6X0RQ0:PnPiP~PSPkP<17G~RzfMRx#9Rw#4Rv'3%4xRY/>U,3zRCP_Q0<PzPz%BzPvP_PWPYO1RvO1P_P_Q0=PwPvPWPxPY%BYCkEjGaQ0`C`S0cPCfNRY#_S0d%4Y#1S0e20=HIS0f103H%1I103J[[S0g%1HR3g00g5RvB0<HI9UWQS0h%1J\v^Q3S0i1SYFS0j%1Y12nFS0k#1\T[S0lfOR3/TFS0mPnPF15nFQ0kCM\bS0n1RnFS0o12{FRv?CvF\`S0p1[{FS0qfRRv/2FS0rQ0r#E5?F\cS0s1ZvFS0tfSRI/5F#=\aS0u1XIFS0vfTRw/2F/Iw\aS0w15wFS0xP:fURz/2FRjP:P4%1[Rh10[JR[ACkk2Pd%1yRkQ0M/0JRgPlPmQ0BPoPp1]:2S0y,VE,hpS0zPtPpAPpsERQPtQ0z9upQFDPDPBb9b;b<X1:1012S0{AC882\M[^1:P1Q0_PeP8O3b8WDWCP9P1O2n2001000000121000000b>b=b7b6b5b4b2b:bEbFbBb?K0;CbWgP1O1%A|P317~5Q0cPCQ0dQ0eQ0fQ0gQ0hQ0iQ0jQ0lQ0mQ0nQ0oQ0pQ0qQ0sQ0tQ0uQ0vQ0wQ0xP:PjP:P4PhP[fWR~/75R|#1PdQ0SPmA8N8LQ0T98L@789PoPpPpQ0UPtPp%lq#F9^:O/J=,OEDQPtPpQ0WPtPpQ0XPtPpQ0YPt1WEuRq9PpsFDFDPDPBb9b;b<X1:X3:X@:XA:Q0[Q0\Q0]Q0^17@5#1[[[[^1:^3:^@:^A:P1P6P?f\RNf[RMP\PxPvfZRQO8b8XDgXCkP9P1O2n2001000000121000000b>b=b7b6b5b4b2b:bEbFbBb?Q0cPCQ0dQ0eQ0fQ0gQ0hQ0iQ0jQ0lQ0mQ0nQ0oQ0pQ0qQ0sQ0tQ0uQ0vQ0wQ0xP:PjP:P4PhP[1>|F/3GPdPlPmQ0KPoPpQ0JPtPp1JqO/erDQPDPBb9b;b<X1:X3:Q0HQ0I/>F/38[^1:^3:P1PGPMPYO3b8XDgXCkP9P1O2n2001000000120000000b>b=b7b6b5b4b2b:bEbFbBb?O3PKP{PiP5PPP1E@,<0XG:,::Q00P:PKPvQ0bP5PPP1E@,<0XG:PIPYPxP1C6X0R,:RP1PKPwPYP5PPP1E@,<0P4Q0FPKPzP3P5PPP9E@P~PvP{P1C6X0R,:RP1Q0aPKfXRKPvP5PPP@E@1|I?1UI?R0%A0'oP71Uw6R7%A7PNfVR7PSP1C6X0R,:RP11Uz>S0FPKP7PS17G7R0fYRi#9Rq#4R|'3%4iRj/>U,30RCP_Q0<P0P0%B0P|P_PWPjO1R|O1P_P_Q0=PqP|PWPiPj%BjCkEjGaPwC`PC%_Q%4QS0b#1Q0fQ0gQ0hQ0i1SQF%1Q12NFRC#1\T[1TMFPNPF15NFPCCM\b1RNFf]RC/2FRj?CjF\`1[CFf^Rj/2FS0HQ0H#E5?F\c1ZjFf_R|/5F#=\a1X|Ff`Rq/2FS0I/Iq\a15qFP:faR0/2FP:P4PhP[fcR[,35PdP4%1wS0J10wJS0KfgRh,35Pn%17S0x10~JS0wQ0SPmQ0T?8<L?88L?89LPoPpPpQ0UPtPp%FAS0T9^:O/J=,OEDQPtPpQ0WPtPpQ0XPtPpQ0YPtAPpuEFDFDPDPBb9b;b<X1:X3:X@:XA:Q0[Q0\Q0]Q0^Q0^[[[[^1:^3:^@:^A:P1PZPXflfkQ0?PCfbRAfjS0?O8b8WJWIP9P1O2n2001000000121000000XDgXCkP9P1O2n2001000000121000000b>b=b7b6b5b4b2b:bEbFbBb?P4107S1HSF9?SVQ0b9KGXP110KZ1H\F9?\VP4Q0E1H^FQ0>%4j5KGP110]VQ0@#=P:%90#4AKG|1Xy:PN%40$0@R]&0:0J0CAKGj]%_A%4A#11SfF%1fQ0L#1\T[Q0fQ0gQ0hQ0i1S[F%1[feR]/2FRV#1\T[fdRg/TFP]PF15]FPVCM\b1R]FffR]/2FRV?CVF\`1[]F12hFRV%EV5?F\c1ZhFfhRV/5F#=\a1XVFfiRV/2F/IV\a15VFP:Q0?/2FP:1TxFPYPF15YF12YFCM\b1RYF123FRV?CVF\`1[3FQ0kQ0k#E5?F\c1ZnF15{F#=\a1X{FQ0r/Iv\a15vFP:12IFP:P4Q0JQ0Kfv#49KGzPnQ0xQ0wP4%1g10gJfz#49KGiPq%1]10hJQ0_P?O1%1X\TQ0A%GPRhQ07#G9i:}R]Q06#GQ0QQ0N3N3NQ0P%9P#G9i:}Q0QQ0OQ05#G3N9Nh]3NQ0R'x'w;plPm%Y>?8@L%YX?86L788%YS?8?L?8<L789PoPpPpQ0UPtPpQ01#lRL#;#F9^:OQ0T'J,OrDQPtPpPpQ0UPtPp%FLRLQ02#l#F9^:OQ0V'J'ODQPtPpPpQ0T/OsPtPpPp1VLrPtPpPpQ0V/OsPtPpPp1V=LPtPpPp1WELQ0C1]:U'J'ePtPpPp1eu=Pt1WErQ0C5PpDLDLDLDLDLDLFDPDPBb9b;b<X1:X3:X@:XA:XY:XZ:X[:X\:X]:Q0ZB0DFX>Rr,I8[Q0Z1I6r[%=S10>@%=X10SX1>SU9K6Z135ZAKSXZ[[[[[[[[^1:^3:^@:^A:^Y:^Z:^[:^\:^]:P1P\PfPZPef|f}p+01@#4PjPGPdQ0MPYPIfnfsPxf{OAb8bXWcWbP9P1O2n2001000000121000000WaWdP9P1O2n2001000000121000000bvbubPbJbIbDbCb>b=b7b6b5b4b2b:bEbFbXbBbKWqWpP9P1O2n2001000000121000000W2WoP9P1O2n2001000000121000000O4WnP1O1Q0F#APRPCP~PXP1C6RXX0RQ0:PNP7PSP1CqCbWiP1O1n200110100021110210104bOPQPwP6P1C6X0R,:RQ00PRPMPzP>P1C6X0RPNP~P7P1C6X0R,:RP1PRP|PQPiP1C6X0RAp:y9PjPiPKPyPZP9PIPe17GKRG%9MRe#4RZ'3%4MRQ/>U,3GRUP_Q0<PGPG%BGPZP_PWPQO1RZO1P_P_Q0=PePZPWPMPQ%BQCkEjGaP7C`PU%_N%4N#1Q0fQ0gQ0hQ0i1SNF%1NQ0H#1\T[1TCFPjPF15jFQ0HCM\b1RjF12|FRj?CjF\`1[|FQ0IQ0I#E5?F\c1ZqF150F#=\a1X0F12AF/IA\a15AFP:12[FP:P4Pk10yJ132I?nIJPfQ0`#1Q0_/0JP4Q0x107J132~Q0w'<Pv%1K10iJPlPmQ0BPoPpQ0z,spPtPp1]:HQ03608:,VE,hpRHPtQ0y=PpE=upHFDPDPBb9b;b<X1:Q0{Q0;[Q0G1328?n8J[[^1:P1PMPIP9O3b8WPWJP9P1O2n2001000000121000000WIWDP9P1O2n2001000000121000000b>b=bCb7b6b5b4b:bEbFbBb?P?P6P1N<0ECbX2XX0RP9P1O2n2001000000121100000brW_WkP9P1O2n2001000000121000000W2Xt:P9P1O2n2001000000121100000b^WeP1O1n200110100021110311104bOW`WlP9P1O2n2001000000121000000W2Xw:P9P1O2n2001000000121100000b^WVWUP9P1O2n2001000000121000000W2WTP9P1O2n2001000000121000000b2WmP1O1Q0D#APRP^P>P6P1C6X0RQ0:P\P6P?P1CqCbWhP1O1n200110100021110210104bOWKWRXL:XN:WfXM;P1H0FXM;WjWSP1O1WSo"). Qed.

(* [comment removed for export] *)
Lemma rchain_push (M : word -> option byte) lo fp ra s0 RC :
  fvalid lo fp -> cell_is (hl_segs L) M (fp - 8) 8 ra -> 4096 <= ra < 2 ^ 64 ->
  cell_is (hl_segs L) M (fp - 16) 8 s0 -> 0 <= s0 < 2 ^ 64 ->
  rchain M fp s0 RC -> rchain M lo fp (ra :: RC).
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Chain"] "h01Mh12RCh22fph32loh42rah52s0p;1p;2p;5p;4p;<p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj10Tg009Tj18Tg00:2j14Tg00:Uj1;Tg00@Lj1@Tg00n<j2>Tg00=oj1<Tg00;7j12Tg00kEj25Tg00>nj11Tg00?Mj53Tg00CIj27Tg00<2j2:Tg00<Oj29Tg00M]j26Tg018\j4?Tg01@6l<=Tg00f1#0R6#0#0R0#0R4#0#0R5#8#4%80#4#;[R7g00`eR2%@2R3f4R1f3R8'>p,1L#<R9f6R:%20,51g00fV#1#1#1#1#1#1#1#1R0P8D3%05#0#0#0#0#0#2/71%26%25':R5,91'6P9f8R9%24,5:P0P1D3g00`Gf5R0'71905'6f:R5P9P:P0C?f;P5f9P9f7P:P0P1P8f2R:f1R9f0R5M<=UUUUUUX13X52X42X22X32X07P0P1P8P:P9P5O6W1X52X42X22W3W0o"). Qed.

(* [comment removed for export] *)
Lemma rchain_lo (M : word -> option byte) lo lo' fp RC :
  rchain M lo fp RC -> fvalid lo fp -> lo' < fp -> rchain M lo' fp RC.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Chain"] "p'0h02H0h12H2h22H1h32H3h42H5h52H4h61zi001zh71Hh82RCi012RCh92H8h:1li021lh;2H7h<3fp0h=3lo0h>2H6h?1Mh@2fpi032fphA2loi042lohB3lo'hC3HlohD3RC0hE1VhF2V'hG2V2hH2V3hI2_HhJ3fp'i053fp'hK3pc1i063pc1hL2rai072rai082z0p;1p;4p;2p;3p;7p;6p;5p;<p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj14Tg009Tj1ITg00:2j1GTg00:Uj1LTg00@Lj1TTg018\R6j40Tg00n<j22Tg00<Oj23Tg00jAj1OTg00;7j1=Tg00kEj2BTg00M=j2?Tg00M]R0j29Tg00lBj4HTg00=Uj36Tg00U:j1@Tg00E1j1STg00m=j2RTg00R@j7Dj6CTg00=oj1PTg00>nj18Tg00?Mj5ATg01=hj7NTg00CIj2>Tg00<2j2MTg01@6l<KTg00JHj2ETg00Q3j6JTg015aj3QTg00`eR4f0R5g00`GR736p=<f1R2=645p=1P4f4R3f3R1f2R8P2P5EJp=:1>72/95p=7f5R7P31B18P2P5DAp=51325,98p=FAQ425p=;g00f1#4R9#4#4R:#4R;#4#4R<#I#G%I:#G#L[R=%T4R>P3P1P2P5C012381331P0f6R?/33p,2ar#O%=;R;'BR@,33%=:R:,?3#<'912?7P2f8RA/3?f7RB/3@1?B:#<'9P013A@1?A:#<f:R0f9RC'2P5130@f;RD/?:#<f=REf<RF'313F@R@1?F:#<RG'9PAP@PGP2P5CHCHWHWGP2P5O2n2001000000120000000W0WIP2P5O2n20010000001200000001273P6PA111D1110A6>10f?R6PEPFPDC0[[[P11225#@118E118F%S4RG=6>Ff@R@,17P5fARH,1?fBRI11BHRJA6>GHRK128C#@fGRLfERMfDRNfCROC0]0]3]1X6411?@P5PJPIA6>GIRJfFRP/22#@fHRQPPPMPNC0]0]3X64P5PJP>PG12LM#@fIRRPLPPP2C0]0X:>12PN#@P>PGPRPQPPP5C0fJRSPQPLPGC0]7X8>PQPLPMPGC0PRPLPPPGC0P2POO1'RW7PNP8POFDW0POP5ECb0X3KPAP5D:b0W1PBP5D:b0W2P8P2P5P1O4W3W1W2W0X<4X=4P8P2P5O31282p,1L#PRKPI1B8:RTg00fV#8#8#8#8#8#8#8#8RUP2DA%4<#4#4#4#4#4#=RV,38,78117O117I11APP511CLPQ110LRWA6>GLRX128FPKfMRYPEP:PUPFE513EV,7EfORZPYfLR[fKR\C0]1]2]0]4]5X6411CPP5PWPQA6>GQRW12[2PKfNR]PTPUPEDAf>R^13^V'7R_fPR`P]PYP[C0]1]2]0]4X64P5PWP>PG12Y\PKPZP[P:PUP^E5136V,76fQRWPZP]P1C0]1]2]0X:>12[SPKP]P\P:PUPEE5P>PGPWP`P]P5C0fRRSP`PZPGC0]7X8>P`PZPYPGC0PWPZP]P@PRP8P2FNW7P[P3P\FDX1_W2W0PRP5ECb0X4XPDP5D:b0W5P0P5D:b0W3P8P2P5P7P3P1O6X4JW5W3W1W2W0XK4X<4X=4P7P3P1P8P2P5O61231PKPRP3P:PUP1E51>V3%=9%=<'MR<7F3PKP\P?P;PUP3E5137<,77PYPAP?P7C0110Y110[1;0A=6>[11E`P511^WPS116WR[1;6E=6>WRW128HPKfWREPIP:PUPHE51>VI?FI<PKfYRYPNP;PUPIE513O<R\,7Of[R9PPPNPOC0f\RJfZRXPYfXR_C0]4]5]3]1]2]0]9];X6411^`P5P[PS1;@^=6>SRSfVR[/22PKP_PTPUPIDA1>VO/9\R\PKPXP3P;PUPOE513N<RT,7NR`PJP?PMPNC0f]R]P9PXPYC0]4]5]3]1]2]0]9X64P5PSP>1;H6fURH,2EPKPYP[P:PUPOE51>VN/9TPKP9P_P;PUPNE513M<,7MP]PXPPPMC0f^R<PJP9P?C0]4]5]3]1]2]0X:>fT,2[PKP_PHP:PUPIE5PKPXPEP;PUPOE5PJPYPMPNC0P>1;LMRMP<P]P9P5C0f_P]PJ1;RLC0]7X8>P]PJPXPMC0P<PJP9PQPLPPP[P7P3P1P8P2M<KW7PYPBP_FDW4X5`W3X1\W2W0fSP5ECb0X9WP@P5D:b0W;P6P5D:b0W>P8P2P5PAPBP?P7P3P1O9W9W;W>W4W5W3W1W2W0XD>XJ4XL4X<4X=4P0PCPAPBP?P7P3P1P8P2P5O;n10410010810200000033010410300061104103106000000000;11041031071051010000000000000000001180118CA6>8CP^PFPDP0C0[[[X:>X64X64PBP7P3O3P51E4A1E4?1E>7O3b0bFWCWEW7X8>X@4XB4XA4X?=P3P1P8P2P5O5W8X@4XB4XA4W?o"). Qed.

Lemma ukey_frame p0 (M M' : word -> option byte) sp ra s0 K :
  ukey p0 M sp ra s0 K -> 16 <= sp -> sp mod 8 = 0 -> ar_stack_top ar < 2 ^ 64 ->
  (forall x : word, sp <= bv_unsigned x < ar_stack_top ar -> M' x = M x) ->
  ukey p0 M' sp ra s0 K.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Chain"] "p'0h02H0h12RCi002RCh22H2h32H1h42H3h52H5h62H4h71xi011xh81zi021zh91Hh:2H8h;2H7h<2H6h=1li031lh>2AGh?2H9h@3HsphA4Hsp8hB4HtophC7__sat10hD7__sat11hE7__sat12hF6__sat9hG2fpi042fphH2loi052lohI1qhJ2q0hK1rhL2r0hM2D1hN2D2hO2HahP1KhQ1MhR2M'hS1UhT7__arithhU4__ffhV7__sat13hW8__varmaphX5__withY4__x1hZ4__x2h[4__x3h\4__x4h]4__x5h^4__x6h_2p0h`2rai062raha2s0hb2sphc1Ehd3Hnehe3Hrahf2Hxhg3NV'hh3RC0hi1Vhj2V'hk2W1hl2W2hm2W3hn7__sat14ho3fp'i073fp'hp3pc1i083pc1hq3ra0hr1si091si0:1fi0;1ni0<2z0p%0p&0p;1p;6p;2p;3p;4p;9p;7p;5p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj1ATg009Tk100Tg00:2j1yTg00:Uk10;Tg00@Lk102Tg01Fnj6JTg01H0k10LTg00n<j24Tg00E1j1wTg00=Uj30Tg00;7j1RTg00<2k20RTg01I7R6j2VTg00CIj27Tg00jAk10ETg00<Oj25Tg00<kj2cTg01IQj3uTg00;Uj2HTg01Ikj3nTg01CNR0j2ZTg018\S00j41Tg00M]R4j26Tg01>nk20TTg00U:j1CTg00iaR5k20STg00kEj2]Tg00Shj2\Tg00M=j28Tg00Cek20QTg00DMk30PTg00TYj2Yj3xTg00USj2:Tg00VMj2XTg00W4j2[Tg00W[j2WTg00XAj2STg00Xgk10NTg00Eok10KTg00FMk10JTg00G[j2mTg00Ifk20ITg00JHj2eTg00Jbk20HTg00KNk30GTg00Kmk40FTg010^j2kTg00V0j2jTg00R@j6Uj7lTg011Ok10DTg011mk20CTg00>nj1KTg0137k30BTg012Nj2vTg014Ij2{Tg0155j2oTg01:hk20ATg01;Qk30@Tg015aj3^Tg00EQj2tTg00YEj4QTg00G8j2LTg016Aj1gTg016fj3sTg00H>j3hTg00IDk10=Tg01<:k30<Tg00\Bj4bTg01BDm90>Tg019bk40?Tg00=ok108Tg00?Mj5aTg00m=j2|Tg00lBj4_Tg01DLk407Tg01JEj2~Tg00\mk706Tg010:k60MTg013`k305Tg00_ck704Tg00]Qk80OTg00Q3k603Tg00`eR7f1R2f0R33^p=3%C2/63p=Tg00`GR1f2R8'71523'6p=;1623,68p=?f3R9/781523'6p=@1H239078p=Ff7R:f6R;f5R<f4R=C11~239098'6p=>%C81Z23'6p=I1823=071p=<1782/63p==A0723p=21713p=91523,68p>0:A0723#Cp=`A^723,~890=9p=dP=P9P8P2C1/63p=q1Z23,68p=}1682/63p>01A0731p=O1j82/H39079p=DP7P2g017IP3Cbp=fP2g00ajR>g00bIR?P?g00biR@P3g00cIK06p=GP2P>P?P?P@P3J0Mp=z1v73p=NB05723p=EP7P2g00ciP3Cbp=iP8P>P?P?P@P2P3K04p=rP9P>P?P?P@P8P2P3L0Op=P1j82/H3p>09P7P=P9P8P2P3J03p=MP<P=1]98P2P3Dap=B1712/63p=pg00f1S01#AS02#AS03#AS04#AR>#A#ARA$00RB#yRCQ04$00#y$0;RD[S05Q05&027REQ05Q05P;P<P9P8P2P3EJP6p,2arRF$0LRG/4=RH%w7RI,3:90E2RJ'T%AA#A#A#A#A#A#RRK9;99=?HJPKP9P9Q02#RRJ%RARA+0RRLC@Q04#RRM9F8=P:P<P9P3PEP8f8RN13=3G>X1E7IE5?H'V%R>R>/7<1<;M&0EFRF/5LRHf9RO1cB3RP15PFRQ3=f;RRP2O1f<RSP2O1RT50D[^7CPSf:RUPOPNP:P;EJ[[[[P314G<RV13NI90E8RW'T17>;1<:MA=UPQf=RXP2O1RY90DT[^7C14GUS0613XI90E:RT'TQ06A;OOK;?TQ06PKPOPOPLC@AFNUMPSPRPOP3PEPNf>RT13U3G>X1E7IE3?'V;u=W>XBHWAW@WSP3O1A;==K=?VWPKP=P=PLC@S071H<MS08,29PNP;P=P3PEP9PO13<3G>X1E7IE5?V'VP614G;R6%9<S09@0:<K13OI90E93?15<LS0:9=K<AF=;MPOP:P<P3PEP=PU13;3G>X1E7IE5?617>:1<NMA=RPQPTP2O1R690DY[^7CPTPSPRPUPOPNEJ[\H[[P314G:RYA;;;K13UI90E=3?17>N1<OMA=SPQf?RVP2O1RW90D6[^7C14GSR613VI90EORZ'TA;RRK=?6ZRZPKPRPRPLC@R[1HSM,`UR\PTPXPRP3PEPUf@R]PSP3DdR^DqX1E7}E5?6R6'VAuZ6=3nW>XBHWAW@WSP3O1PKP;P;PLC@AF<:MPUPNP;P3PEP<PR13:3G>X1E7IE5?YP414GN17K:15:LAF;NMPRPOP:P3PEP;PS13N3G>X1E7IE40117>O1<UMA=XPQP]P2O190DW[^7CP]PTPXPSPRPUEJ[\H[[P3Q0617KU15ULAFORMPTPSPUP3PEPOPV13R3G>X1E7IE401P4P[PVPXPRP3P^DqX1E9}\E17>X1<TMfAR\?=PQfCR^P2O1fDR[P2O150D[^7CP[fBRWP\P]PVPTEJ[\H[[P3PKPXPXPLC@AFXVMPWP]PTP3PEPXP^13V3G>X1E7IEP41H]M,`TP^P\PVP3PEPTP[13]3G>X1E,ZE17>\1<WMfERY?=PQfGR6P2O1fHRZP2O150D[^7CPZfFR_PYP[P^PWEJ[\H[[P31HWM,`]P_P[PWP3PEP\P613^3G>X1E,ZEP0PEP6PYP^P3PEPWPZ13[3G>X1E17>Y1<_MfIR0?=PQfKS0;P2O1fLR`P2O150D[^7CP`fJRaP0PZP6P_EJ[\H[[P3P0P6PYP3PEP[Pa13_3G>P4PaPZP_P2C1PEPYQ0;P6P2Dd17>01<aMfMRb?=PQfORcP2O1fPRdP2O150D[^7CPdfNRePbP`Q0;PaEJ[\H[[P3P`PaPZP9C1PEPZPePaP=Dd17>`1<bMA=dPQfRRfP2O1fSRgP2O150D[^7C14GdRG13gI90EbRD'TA;ccK=?GDS0<PKPcPcPLC@RD1HdM,`eRhPffQRiPcP3PEPefTRj13d3G>X1ERk,ZERl'6Rm'6Rn,6GS0='VQ0<Q0=PGPnPYPDPmP\PhPlPXPEPkPOPiPdPePOC1PEPbPgPcPODd20Tde14deRb%Cb+0SP514icR5%C5PgPfPdPRC1P314fdS0>fUR5PjPgPiPSPNP;P=1]f>?=PQP<P2P4155g1]F>RQ,5g1<gM'6fVRP1cB8RbPbPFC@P8fWRb/5515PQ1<PM'6P415bQ1<bMfZS0?1cB;R4P4PFC@P3fYS0@/5QQ0?/<Mf[RQ1\QM%9Q%9MR4f]Rk/8MS0A#9[[f^Rl/\M%9lS0Bf`Rh/8MS0C#9\4[20QJAS0D151J%9A151L[[S0E%9JRmg00g5RDB0PJA2UWOS0F%9L\D^OmS0GfaRm/YMS0H%OMRD#CRAfbRJPM1:JM18JMCD[S0I1XJMS0J151MRnfcRG/8MRo?;oM[S0K1[GMS0L15M1RofdRp/8MS0M,5MQ0M/71'6[S0N1WpMS0OfeRq/:MS0P#O\DS0Q1SqMS0RffRr/8MS0S/2r\DS0T1:rMS0UP7fgRs/8MRtP71YrMPsPM1:sMPtCD\A1XsMfhRu/8MRv?;vM\n1[uMfiRw/8MRx,5M17x1'6\o1WwMfjRx/:MS0V#O\D1SxMfkRy/8MS0W/2y\D1:yMS0XP7flRz/8MR{P7g00gQR|#wS0Y&02|S0Z&0N7S0[&0K7S0\&0J7R}1m7MS0]1m71S0^'f,G}'z20I}@S0_P3P8g00h=R@g00h]R~'e20H38=0@~dB0G712H0FS0`bUbWbXg00o]S0a\DP3bTS0bbLbJb?b:b;b<b5bKbIb6b4b2b3b0bFbCbDbE7xMPQPM1:QM18QMCDf\S0c/\MQ0c#918lMS0d#9\4[f_S0e/\MS0fQ0e#918mM#9\4[S0g1klMQ0B1:hMS0h#9\4[Q0DQ0EQ0FQ0GQ0HQ0IQ0JQ0KQ0LQ0NQ0OQ0QQ0RQ0TQ0UP7PtP71YxMPyPMQ0XQ0WCD\A1XyMA;{{M\n1[zMfmR{/8MR~,5M17~1'6\o1W{MfnR~/:M#O\D1S~MfoR@/8MS0X/2@\D1:@MS0TP7fpS0R/8MS0QP7Q0bbLbJb?b:b;b<b5bKbIb6b4b2b3b0bFbCbDbEbV9xlM1:lM,jMS0bQ0d5FlP7Q0AQ0b=Fl3X87P2P1P8EUPkPM1:kMP1CDP7Q0CPmPM1:mMP3CDX87P2P1PWEUPhPMQ0hP1CDQ0fQ0g1\JM%9JS0gQ0M#9\4[1kGM%9GQ0P#9\4[1kJMQ0g1:pM#9\4[Q0DQ0EQ0FQ0G1YqMPrPMQ0UQ0SCD\A1XrMA;ttM\n1[sM15Mv17v1'6\o1WuM1:wM#O\D1SwM18xM/2x\DQ0VP7Q0WP71Y~MP@PMQ0TQ0XCD\A1X@MQ0QQ0Q;;M\nQ0R/[MfqRn/8MR@,5M17@1'6\o1WnMfrRo/:M#O\D1SoMfsR@/8M/2@\D1:@MP7ftRD/8MP7Q01$0D-0C7g00fVS0Q#KS0X#KS0T#KRA#K#K#KRv#KRt#N60B7R4%NvS0W%NA'E'E%KtRt#NS0VQ0T#N,E4'EQ0X#NRAQ0Q,v7Rv'Eg0180S0Q'{'o'oQ0W/EA,E4R420A7M>0@7vQ0V/E4'EQ0Q'{'oQ0Y5^|5^|Q0ZP7P7P71t7<P;Q0[CQP8Q0[CQP2P7P71t7;P=Q0[CQP9Q0[CQCQQ0\P}Q01,L7R|Q0]Q03#g,L75s7Q0^5h7'f,G}&0=?R?P}Q02#g,L7R4Q0]Q04,L75s7Q0^5h7'f,G}P?P}1m7>Rv:0<74Q02,L7RA'i,G}P7PAg00aCS02Q01#g,L7Cb,G}S015r}P?P}P7P|Q02P4Cb,G}P?P}1iv|,G}P?P}Q0]9h7|,f4,G},z}P?1i|A,G}Q015r}CPCPCPCPCPCPQ0_Q0`bUbWbXXY7XZ7X[7X\7X]7X^7B09M<1R1,2312=11]<>P9P9P=C@159;17>=Q08,2NQ0a[P;P:P:PNC@[[[[[[^Y7^Z7^[7^\7^]7^^7P3P8POPDPF1cBffvRBPYP_PiPeQ0@PGO<bTbLbJb?b:b;b<b5bKbIb6b4b2b3b0bFbCbDbEbVbnbNbMbNbMWmWlP2P3O2n2001000000121000000W0WkP2P3O2n2001000000121000000O2WfX7CN90>WjP3O1Q0>#CQ00P5129b129PA0E9WPQQ0?fXRCP^C1[[[PN1423#CQ0@,28128CA0EI[Q0c,2<P312;kPl12:kRCA0EI0Re148O#CPGPJPhQ0;C1]0]4]2X87Q0c,2;P3PCPlA0EIaRa14J2#CPpPGPmP`C1]0]4X87P3PaPEPI14Gm#CPqPpPJP2C1]0X=E14Jh#CPEPIPrPpPJP3C1PrPqPGPIC1]9X1EPqPGPmPIC1PqPpPJP\H0?W9P`P8PZFlW0Q0;P3EUb0X4ePNP3DMb0W2P:P3DMb0W3P8P2P3P9O4W4W2W3W0XG7XH7P8P2P3O31482p,1L$08ReQ0e1]8MR`PtP2DaA;88KQ0e,2<12<l12NJP312OGPp12UGRGA0EIcRc148SPePxPXPMPtPSEBA;XXKPyPxPuPgC1]2]3]0]5]6X8712OJP3PGPpA0EIdRp14u2PePyP`PtPXDaA;TTKRGPzPyPwPjC1]2]3]0]5X87P3PpPEPI14wsPePzPuPMPtPTEBA;VVKP{PzPxP9C1]2]3]0X=E14urPePyPsPMPtPXEBPEPIP~PzPxP3C1P~P{PyPIC1]9X1EP{PyPwPIC1P{PzPxPIC1P0P9O1'|W9PjP=PdFlX2GW3W0PiP3EUb0X5cPRP3DMb0W6PUP3DMb0W4P8P2P3P<P=P9O6X5aW6W4W2W3W0Xp7XG7XH7P<P=P9P8P2P3O614=9PePrP=PMPtP9EBQ07PePuP;P>PtP=EBQ09Q0:'6PxPNP;P<C112Uw12Uu13UN=0Ej12XzP312T{P~12V{R{13VXQ0@50ERu148\PePDPWPMPtP\EBPKPWPWPLC@PePBP[P>PtPWEB15^LRw,p^fxRxP_P[P^C1PxfwRrfuRaPhC1]5]6]4]2]3]0]:];X8712TzP3P{P~13]TQ0?50ERT14o2PePaP`PtPWDaA=K^wRwPePrP=P>PtP^EB15[LR`,p[R~fyR{P;PYP[C1P{PxPBPmC1]5]6]4]2]3]0]:X87P3PTPE13\V14@nPePBPoPMPtP^EBA=K[`PePxPDP>PtP[EBA;YYLfzRLPBP_PYC1PLP{PrP;C1]5]6]4]2]3]0X=EQ0R,4oPePaPnPMPtPWEBPePrP@P>PtP^EBP{PaPYP[C1PE136YRYf{R[P{PrP3C1P[PLPx1306C1]9X1EPLPxPBPYC1PLP{Pr13Z_C1PPP;O1'|W9PmP:PkFlW5X6~W4X2wW3W0PQP3EUb0X:uP]P3DMb0W;PVP3DMb0W<P8P2P3PNP:P;P<P=P9O9W:W;W<W5W6W4W2W3W0XhEXo7Xq7XG7XH7PUPOPNP:P;P<P=P9P8P2P3O;n10410210<10300000033010510400061105104108000000000;1105104106107100000000000000000000128P1285A0E8\Q0?Q0@PbPWC1[[[X=EX87X87PgPiPSO3P31e7j1e7f1eEXO3b0WgP3O1n200110900021110:1110;brP=C_H07C_C_C_3n3nW>XBHWAW@WcW9P2P3O2n2001000000121000000W0X1EP2P3O2n2001000000121101000W0WdP2P3O2n2001000000121000000W0WeP2P3O2n2001000000121000000W0WiP2P3O2n2001000000121000000W0P3O1n200100000021100011000W0P3O1n200100000021100011000W0XPEXa7X`7Xb7WRWQX_7P;P<P=P9P8P2P3O7WPXa7X`7Xb7WRWQX_7o"). Qed.

(* [comment removed for export] *)
Lemma ukey_intro p0 (M : word -> option byte) sp ra s0 RC :
  fvalid (ar_stack_bottom ar) sp -> 4096 <= ra < 2 ^ 64 -> s0 <> sp + 8 -> rchain M sp s0 RC -> ukey p0 M sp ra s0 (akey p0 (ra :: RC)).
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Chain"] "h02RCh11Mh22p0h32rah42s0h52sph61Hh73Hneh83Hrah91Vp;1p;2p;3p;4p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj13Tg009Tj1?Tg00:2j1<Tg00:Uj1ITg00@Lj1HTg01H0j1GTg00n<j2>Tg00;7j14Tg00CIj28Tg00<2j2ATg00<Oj29Tg00M]j20Tg00;Uj2@Tg00=Uj31Tg00U:j1;Tg018\j4:Tg015aj35Tg01JEj27Tg00E1j1FTg01CNj2ETg01I7j2DTg00JHj2CTg00lBj46Tg01DLj4BTg01Ikj3=Tf0R6#3#3p=2g00`eR0g00f1#3R4#2R5#3#2R7#?#<%?5#<#I[R2%H0R3p,2ar#GR1f3R8'>%27#2#2#4R9/88%44%47'AR7,98'0f5R4%45R5'@9108#;f7R:f6R;f4R<P8C:1>1:R1#;f9R=A50;<'7R>%F0950=513R?'0g00`G/8;19;9'0/0?,01R?189;19;7'0R71@:59104#;R5P=f8R=P;P6C:f:R;A50:4'7A50:6,7;513'0X03R;,E3R9'0R@'0RA,01RB'DP1PAP8P7P@f2R@P5P9f1R9P3P;P<P=P:P4P<C:A13>>P61C3>C6CBC6C6C69=?B3=W6W7W8W9X03X40X30X50X12X20P4P<P8P@P9P6O6W0X40X30X50W1W2o"). Qed.
End Chain.

(* [comment removed for export] *)
Section Fam.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.
Variable LR_ : layoutR.
Variable HIk : list (list Z) -> asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

(* [comment removed for export] *)
Definition amalloc_postG (Dp : list (list Z)) (crp : credit) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet) : Prop :=
  forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)) (u : Z),
    getr R' 10%bv = Z_to_bv 64 u ->
    regs_preserved R R' ->
    ablock_range L ar u n -> blocks_apart u n LB -> fframes_apart u n (FF ++ LK) ->
    defined M' u n -> shadow_blk M' u n ->
    aheap_pres L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_malloc L) M M' ->
    model_rt model model' -> incl A A' -> MInv A' model' ->
    ri_inv (HIk Dp) ((u, n) :: LB) FF LK crp A' M' (vml_of model') ->
    srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K.
Definition afree_postG (Dp : list (list Z)) (crp : credit) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (u : Z) (K : ShapeAlg.TSet) : Prop :=
  forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
    regs_preserved R R' ->
    aheap_pres L ar (lb_remove u LB) FF (bv_unsigned (getr R 2%bv)) (hl_scr_free L) M M' ->
    model_rt model model' -> incl A A' -> MInv A' model' ->
    ri_inv (HIk Dp) (lb_remove u LB) FF LK crp A' M' (vml_of model') ->
    srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K.

(* [comment removed for export] *)
Definition amalloc_preG (D : list (list Z)) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet) : Prop :=
  ri_inv (HIk D) LB FF LK cr A M (vml_of model) /\ m_halted model = None /\ MInv A model /\
  getr R 10%bv = Z_to_bv 64 n /\
  getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ Hoare.ret_ok (getr R 1%bv) /\
  astack_ok L ar M (hl_scr_malloc L) (bv_unsigned (getr R 2%bv)) /\
  K [].
Definition afree_preG (D : list (list Z)) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (u n : Z) (K : ShapeAlg.TSet) : Prop :=
  ri_inv (HIk D) LB FF LK cr A M (vml_of model) /\ m_halted model = None /\ MInv A model /\
  In (u, n) LB /\ getr R 10%bv = Z_to_bv 64 u /\
  getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ Hoare.ret_ok (getr R 1%bv) /\
  astack_ok L ar M (hl_scr_free L) (bv_unsigned (getr R 2%bv)) /\
  K [].
(* [comment removed for export] *)
Definition ukey_at (p0 : Z) (R : bvmap 5 word) (M : word -> option byte) (Kt : list Z) : Prop :=
  ukey L ar p0 M (bv_unsigned (getr R 2%bv)) (bv_unsigned (getr R 1%bv)) (bv_unsigned (getr R 8%bv)) Kt.

(* [comment removed for export] *)
Definition amallocN_spec : Prop :=
  forall D fx R M model LB FF LK cr A n K,
    amalloc_preG D fx R M model LB FF LK cr A n K -> 0 < n <= NREQ -> acredit_ok L cr n ->
    amalloc_postG D (adebit L cr n) fx R M model LB FF LK A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.
(* [comment removed for export] *)
Definition amallocL_spec : Prop :=
  forall D fx R M model LB FF LK cr A n K Kt,
    amalloc_preG D fx R M model LB FF LK cr A n K -> 0 < n <= NREQ -> acredit_ok L cr n ->
    ukey_at (hlr_pc_malloc LR_) R M Kt ->
    amalloc_postG (Kt :: D) (adebit L cr n) fx R M model LB FF LK A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.
Definition afreeL_spec : Prop :=
  forall D fx R M model LB FF LK cr A u n K Kt,
    afree_preG D fx R M model LB FF LK cr A u n K ->
    ukey_at (hlr_pc_free LR_) R M Kt ->
    afree_postG (Kt :: D) cr fx R M model LB FF LK A u K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_free L)) M model) K.
(* [comment removed for export] *)
Definition amallocW_spec : Prop :=
  forall D fx R M model LB FF LK cr A n K Kt,
    amalloc_preG D fx R M model LB FF LK cr A n K -> NW_LO <= n <= NW_HI -> 1 <= fst cr ->
    ukey_at (hlr_pc_malloc LR_) R M Kt -> In Kt D ->
    amalloc_postG D (fst cr - 1, snd cr) fx R M model LB FF LK A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.
Definition afreeW_spec : Prop :=
  forall D fx R M model LB FF LK cr A u n K Kt,
    afree_preG D fx R M model LB FF LK cr A u n K -> NW_LO <= n <= NW_HI ->
    ukey_at (hlr_pc_free LR_) R M Kt -> In Kt D ->
    afree_postG D (fst cr + 1, snd cr) fx R M model LB FF LK A u K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_free L)) M model) K.

(* [comment removed for export] *)
Definition amemN_pre (D : list (list Z)) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dst n : Z) (K : ShapeAlg.TSet) : Prop :=
  ri_inv (HIk D) LB FF LK cr A M (vml_of model) /\ m_halted model = None /\ MInv A model /\
  getr R 10%bv = Z_to_bv 64 dst /\ getr R 12%bv = Z_to_bv 64 n /\ 0 <= n <= NREQ /\
  getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ Hoare.ret_ok (getr R 1%bv) /\
  astack_ok L ar M (hl_scr_mem L) (bv_unsigned (getr R 2%bv)) /\
  aacc M dst n /\ (forall i, 0 <= i < n -> aclientw L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (dst + i)) /\
  (forall i (m : nat), 0 <= i -> i + Z.of_nat m <= n -> store_ok (hl_segs L) M (Z_to_bv 64 (dst + i)) m = true) /\
  K [] /\ app_rng ar dst n.
Definition amemsetN_spec : Prop :=
  forall D fx R M model LB FF LK cr A dst c n K,
    amemN_pre D fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 c ->
    amem_post L ar scfg (HIk D) fx R M model LB FF LK cr A dst n (fun _ v => v = c mod 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_asan_memset L)) M model) K.
Definition amemcpyN_spec_at (pc : Z) : Prop :=
  forall D fx R M model LB FF LK cr A dst src n (bs : list byte) K,
    amemN_pre D fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 src ->
    aacc M src n -> 0 <= src /\ src + n <= 2 ^ 47 -> app_rng ar src n ->
    (forall i, 0 <= i < n -> hl_img_lo L <= src + i < hl_img_hi L \/ aclient L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (src + i)) ->
    rdn (hl_segs L) M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
    (dst + n <= src \/ src + n <= dst) ->
    amem_post L ar scfg (HIk D) fx R M model LB FF LK cr A dst n (fun i v => nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.

(* [comment removed for export] *)
Definition rt_weakenR : Prop :=
  forall D0 D1 LB FF LK cr cr' A M V,
    ri_inv (HIk D1) LB FF LK cr A M V -> incl D0 D1 ->
    0 <= fst cr' <= fst cr -> 0 <= snd cr' <= snd cr ->
    ri_inv (HIk D0) LB FF LK cr' A M V.

(* [comment removed for export] *)
Record asan_famR_ok : Prop := AFROK {
  fr_base    : forall D, HAJ.asan_iface_okR L ar C scfg (HIk D);
  fr_weaken  : rt_weakenR;
  fr_mallocN : amallocN_spec;
  fr_memsetN : amemsetN_spec;
  fr_memcpyN : amemcpyN_spec_at (hl_asan_memcpy L);
  fr_memmoveN : amemcpyN_spec_at (hl_asan_memmove L);
  fr_mallocL : amallocL_spec;
  fr_freeL   : afreeL_spec;
  fr_mallocW : amallocW_spec;
  fr_freeW   : afreeW_spec
}.

(* [comment removed for export] *)
Definition kin (Kt : list Z) (D : list (list Z)) : bool :=
  existsb (fun k => if list_eq_dec Z.eq_dec k Kt then true else false) D.
Lemma kin_In Kt D : kin Kt D = true -> In Kt D.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Fam"] "p'0h01Eh11kh21xi001xh31Hh42Hkh51Dh62Kth71ei011eh81Ah91Bh:5lemmah;1ni021nh<1si031sh=1yi041bp;1p;3p;2p;4p;8p;=p;7p;6p-1R0g01KGR1p4p710p9P0g000SR2p4p710p9P0P2p4p7210p9P0P2p4p73110p9P0g01KnR3p4p710p9P0g01L]R4p4p710p9P0g01M?R5p4p710R6p8P0p1002gR7p4p710R8p8P0P7p4p7210p8P0p1003Cp4p710R7p8P0p1003dR9p4p710p8P0P9p4p7210p8P0p1004AR9p4p710R:p8P0P9p4p7210R9p8P0p1004Up4p710R;p8P0p10051p4p710R0p8p1005Jp605000R<P6p8P<P8p8P<P7p8P<p1006Hp4p710p8P<p1006mp4p710p8P<p1007Mp4p710p8P<p1007jR7p4p710p8P<P7p4p7210p8P<g008>R7p4p710p8P<P0p8p1008Zp4p710R0P:p8P0P9p8P0P;p8g00@Lj1:Tg00=Uj31Tg00U:j13TP7j39TP5j30Tg00M]R5j25Tg01CNR7j27Tg01MVR;j2=TP1j46TP2j4<Tg01Moj2;Tg01N\R2j2ITP4j4HTg01O:j88Tg01Omj3GTg01Pcj4FTP3l=ETg01QVj3CTg00iaR3j2BTg00Q3j7ATg00R@j6@Tg00m=j2?Tg01R9j2DTg01S:j4>Tg00`eR4g00kbf1R1f0R0C>p=4g00h=R9g00h]R:710p=2%:4R4%:4R<P3f2R89140R6%36P91408P:g01SZR6n200100000021000010000R=X14R>=940#2A0401R?P3f3R@9140RA%3AP9140@P:P6n200100000021000010000RAX14RBP0O1#2'5X24,74'=p-0RCPC^9CRD]8PCPC\CP;PCPCP;P;C6REC6P2g01T:PCPDP;PCPCP;PCPCPCP2C<R2C6RFC6g00cIPCPDP;P;1;C;RDPEPFPCPCP;P;PDP;P2PCP;1I01X=CX2Cg01U5CHG8G8A94B1#2A0408RBP3f4R29140RD%3DP91402P:P6n200100000021000010000X14P0O1#2'5X24,74P0A0481RDPDPCP;g01Uk9GC;PDCFM=EW:AC4>0%2=,5?X24,74P7P4%2A,5BX24A04@8P0A0402P3f5R89140RB%3BP91408P:P6n200100000021000010000#2'5P5A0418P3f6R59141RB%3BP91415P:P6n200100000021000010000#2f7RB=045P0A04@BP3f9R@9142RA%3AP9142@P:P6n200100000021000010000#2f:R@,48A148@R@%3@'BP3f;9145R5%35P3f<R3914BRB%3BR5P9P0P:P6n200100000021000010000#2f=R@=043R3]0P0P4P@A040@A19::R@f@f?R8504]0]4X14P1X0@X43f8P0P2FAX7BP0O1A196:P9P6P9PCP0g00o]RCg00g5n0110400020000X79g01V[P:P0E@PCf>9048/?0b3W0X;5P0O1n200110300021010110102P1O1b<W0W4P1P0O2n2001000000120000000W3X14P1P0O2n2001000000121100000W3O21D10#2PD[eX5<X64P1P0O2W5W6o"). Qed.
Definition warm_ok (Kt : list Z) (D : list (list Z)) (n : Z) : bool := kin Kt D && (NW_LO <=? n) && (n <=? NW_HI).
Definition amallocU_spec : Prop :=
  forall D fx R M model LB FF LK cr A n K Kt,
    amalloc_preG D fx R M model LB FF LK cr A n K -> 0 < n <= NREQ ->
    ukey_at (hlr_pc_malloc LR_) R M Kt ->
    (if warm_ok Kt D n then 1 <= fst cr else acredit_ok L cr n) ->
    amalloc_postG (Kt :: D) (if warm_ok Kt D n then (fst cr - 1, snd cr) else adebit L cr n) fx R M model LB FF LK A n K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_malloc L)) M model) K.
Definition afreeU_spec : Prop :=
  forall D fx R M model LB FF LK cr A u n K Kt,
    afree_preG D fx R M model LB FF LK cr A u n K ->
    ukey_at (hlr_pc_free LR_) R M Kt ->
    afree_postG (Kt :: D) (if warm_ok Kt D n then (fst cr + 1, snd cr) else cr) fx R M model LB FF LK A u K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_free L)) M model) K.

Section Derived.
Hypothesis OK : asan_famR_ok.

Lemma warm_ok_facts Kt D n : warm_ok Kt D n = true -> In Kt D /\ NW_LO <= n <= NW_HI.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Fam"; "Derived"] "h01Hh11nh21Dh32H2h42H3h52Kth64__x1h74__x2h84__x3h95lemmah:1mh;1Ah<1Bh=2H1h>7__arithh?4__ffh@8__varmaphA5__withB1xhC1yp;1p;2p;4p;8p;3p;6p;7p;=p-1R0g01KGR1p4p710p9P0g000SR2p4p710p9P0P2p4p7210p9P0P2p4p73110p9P0g01KnR3p4p710p9P0g01L]R4p4p710p9P0g01M?R5p4p710R6p8P0p1002gR7p4p710R8p8P0P7p4p7210p8P0p1003Cp4p710R7p8P0p1003dR9p4p710p8P0P9p4p7210p8P0p1004AR9p4p710R:p8P0P9p4p7210R9p8P0p1004Up4p710R;p8P0p10051p4p710R0p8p1005Jp605000R<P6p8P<P8p8P<P7p8P<p1006Hp4p710p8P<p1006mp4p710p8P<p1007Mp4p710p8P<p1007jR7p4p710p8P<P7p4p7210p8P<p1008>p4p710p8P<P0p8p1008Zp4p710R0P:p8P0P9p8P0P;p8g00@Lj19Tg01R9j24Tg01W7j23Tg01WTj26Tg00M]R;j22Tg01MVR0j2>TP1j45TP2j4LTg01Moj2GTg01N\R2j2FTP4j4DTg01O:j8:TP5j37Tg00CIj21Tg01Omj3WTg01Pcj4BTg01X2j2@Tg01XSj6VTg01YEj3UTg01ZIj2TTg00E1j1NTg00EQj2=Tg00YEj4MTg00Eoj1KTg00FMj1JTg008oj1HTg00G8j28Tg016Aj1ITg00\Bj4;Tg00IDj1ETg00_cj7OTg00Ifj2PTg00JHj2QTg00Jbj2CTg00KNj3RTg00Kmj4STg00lBj4]Tg01Zij3\Tg00=Uj3[TP3l=ZTg00\mj7YTg00]Qj8XTg00h=R3f0R5g00h]R43[p=0P5f1R1P2g01T:f2R9g00cIR:f3R<f4R7f5R8f6R6f7R=f8R>f9R?M=Zp=AP1g00ajR@g00bIRAPAg00biRBP5P:FYp=<P<P@PAPAPBP9P1P5GXp=?g00`eR:#9RC%9CRD1491REg01[nRF/35RG'6RHg01]1RI,35RJ'6#0%0HRK%0JRL'2'>p-0RMPM^<MRN];ROPMPM\MP0PMPMP0P0C5RPC5RQPMPNP0PMPMP0PMPMPMP2CLR2C5RRC5RSPMPNP0P01GM0RNPPPRPMPMP0P0PNP0P2PMP01F51XCMXBMg01U5CDG:G:R214<9RN13F1RR'6RP131IRT'6#0%0PRP%0TRT'2RUP5A7C<911F1111I'2'2RVPVPMP0g01Uk9WM0RWPVCBRXM:AW91@HJ%0E%0G'2RJ,>KPOPQPSP2PU%0N%0R'2RR/2TPPPRP5PTPTPMP0PWPTCBEVPVPVPXM:AW91@EG12JLP;PRPTA7C7<11F9119I'2'2P51487#013F<#0'2P;1468#013F7#0138I#0A7C>=11F6116I'2'2[P514>=#013F=#013>I#0f;R>f:R=57C11F?11?I'2AU>=9P;1315#01191[R;11151391#0R>[11<9\>1T15P1n2001000000120000000X::X1:R>P;^::^1:R;P5PFP=P9O311F=P>P;P5f<R;PIP<O311;Ig00gQR;#N%9;P:1=:9P11=:<CM%K:%J:R;P:g00f1R>#H,8:R=g00ciR?%I>,8:C;,<;R6%EAR8P;P:18:>P?P=C;,<;R=P8P;P@PAPAPBP=P6FOC?C?1P;BP5P91Q341C59#0dg00`G=R:1CSb?b@bAX6:X7:X8:1119R4119<11<7'2\4[^6:^7:^8:P5PIf>PFP1P<O5b>b4b0b3b0C]W4W3W=P1P5O2n2001000000121000000W0P1P5O2n2001000000121000000W0O2O2A\915#0PV[eX1:X2DX5CP9P1P5O3X1:W2W5o"). Qed.

(* [comment removed for export] *)
Lemma amalloc_postG_known D Kt crp fx R M model LB FF LK A n K :
  In Kt D -> 0 <= fst crp -> 0 <= snd crp ->
  amalloc_postG (Kt :: D) crp fx R M model LB FF LK A n K -> amalloc_postG D crp fx R M model LB FF LK A n K.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Fam"; "Derived"] "h01Ah11Dh22FFh31Hh41Kh52Kth62LBh72LKh81Mh91Rh:7__arithh;4__x1h<3crph=2fxh>1kh?5modelh@1nhA2A'hB2E1hC3E10hD3E11hE2E2hF2E3hG2E4hH2E5hI2E6hJ2E7hK2E8hL2E9hM2H1hN2H2hO3HinhP2HkhQ2M'hR1PhS2R'hT2RIhU4__ffhV8__varmaphW5__withX6model'hY1up;1p;2p;3p;<p;4p;8p;6p;7p;?p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0g01M?R1p4p710R2p8P0p1002gR3p4p710R4p8P0P3p4p7210p8P0p1003Cp4p710R3p8P0g003dR5p4p710p8P0P5p4p7210p8P0p1004AR6p4p710R7p8P0P6p4p7210R6p8P0p1004Up4p710R8p8P0g0051R0p4p710R9p8g005JR:p605000R;P2p8P;P4p8P;P3p8P;p1006Hp4p710p8P;p1006mp4p710p8P;g007MR3p4p710p8P;p1007jR4p4p710p8P;P4p4p7210p8P;p1008>p4p710p8P;P9p8p1008Zp4p710R9P7p8P9P6p8P9P8p8g00@Lj12Tg01^4j2fTg008oj10Tg016Aj1FTg009Tj16Tg00:2j1<Tg01^Tj2WTg00:Uj1OTP1j34TP5j37Tg00CIj21Tg01_@j3:Tg015aj33Tg01_]l<BTg00;7j1;Tg01`hj3>Tg01aKj2=Tg00@lj2XTg00=Uj35Tg01b=j2VTg01cBj4UTg01dFj3TTP3j3NTg01eIj3MTg01fNj3LTg01gLj3KTg00<kj2JTg01hNj1HTg01iSj8GTg01jUj2ITP0j38Tg01kUj2ETg01lQj49Tg01m1j1@Tg01moj8DTg00R@j6PTg00E1j1QTg00EQj2CTg00Eoj1RTg00FMj1STg00G[j2eTg00G8j2dTg00\Bj4ATg00IDj1cTg00_cj7bTg00]Qj8]Tg00Ifj2\Tg00JHj2[Tg00Jbj2ZTg00KNj3YTg00Kmj4^Tg00M]j2_Tg01nml?`Tg00\mj7aTf1R0g00ajR3g00bIR5P5g00biR1f0R8g00cIFap=?g00`eR9#2R6#2R71f99R;g0204R4g00f1R2#0R<#FR=#6R>%0<#0R?#0#0#0#6R@#<RA'WRB%6?#<#O\AR?g020kRC%2;RD%2:REg021aRFf;RGf<RH546g00`GRIA799G'1A:99H,1If>RJf?RK536f=RLPHPGf:RMf9RNf8ROf7RPf6RQf5RRf4RSf3RTM<B%0=#;g01V[R=5>>,=S1X@855AfB/VRp,1LRAp,2arRUf2RVPHCUfARW9TTLf@RX9N:W9MSJALORKAKNQXPAPUfERUfDR:fHRY%;<=>>='=,J@%HAfGRAPMGG1IAMA8;:M1EGHp,3HIkfPR@O1P9P9PGPUC9fIRU53;PYPAfNPHPJ%@LGDPWPXPKPJPLPHPGPMPNPOPPPQPRPSPTPVP0p,2OKfQRW936@RAPWP9P9PHfFC9fJ53;PUPYfORUPUPLPK%@JP8fRRK936W9468g01I7A56K0fSRK9460fTRU946VR=P8A56KVP6PUfV9468X>6PYPTP8EPW3P8O1P8XP=P8O1n200100000021000010000W3X>6A86AWeg00gQRA#Q%2A1C90%R9%S9RAP3P5P5P1P91e9Ig00ciRW1d92R2CA,?AR=%c5PAP3P5P5P1P=P9P2PWP2CA,?AFbG]1\A1P8PVg00h=RAg00h]R1'[1Z8V=5A1dAY9I0C^bUbVbWX;9R111I811I01100'_[^;9RIP8A799@P:O2b:P1PIP8A:99@fCO2b:M?`OAWTWDWCWLWKWJWIWHWGWFWEWBXY9XADXXCXQ?XSBPXPJPLPHPGPMPNPOPPPQPRPSM<BeWRWNWMWOX4FX@9X0DX7EX2EX6DX?CX8?X9BX=4X<;X56X17PHPGPMPNPOPPPQPRPSPTPVP0P8O=W4X@9X0DX7EW2W6W?W8W9W=W<X56W1o"). Qed.
Lemma afree_postG_known D Kt crp fx R M model LB FF LK A u K :
  In Kt D -> 0 <= fst crp -> 0 <= snd crp ->
  afree_postG (Kt :: D) crp fx R M model LB FF LK A u K -> afree_postG D crp fx R M model LB FF LK A u K.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Fam"; "Derived"] "h01Ah11Dh22FFh31Hh41Kh52Kth62LBh72LKh81Mh91Rh:7__arithh;4__x1h<3crph=2fxh>1kh?5modelh@1uhA2A'hB2E1hC2E2hD2E3hE2E4hF2E5hG2H1hH2H2hI3HinhJ2HkhK2M'hL1PhM2R'hN2RIhO4__ffhP8__varmaphQ5__withR6model'p;1p;2p;3p;<p;8p;6p;4p;7p;?p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0g01M?R1p4p710R2p8P0p1002gR3p4p710R4p8P0P3p4p7210p8P0p1003Cp4p710R3p8P0g003dR5p4p710p8P0P5p4p7210p8P0p1004AR6p4p710R7p8P0P6p4p7210R6p8P0p1004Up4p710R8p8P0g0051R0p4p710R9p8g005JR:p605000R;P2p8P;P4p8P;P3p8P;p1006Hp4p710p8P;p1006mp4p710p8P;p1007Mp4p710p8P;p1007jR3p4p710p8P;P3p4p7210p8P;p1008>p4p710p8P;P9p8p1008Zp4p710R9P7p8P9P6p8P9P8p8g00@Lj12Tg01^4j2_Tg008oj10Tg016Aj1CTg009Tj16Tg00:2j1>Tg01^Tj2PTg00:Uj1HTP1j33TP5j3:Tg00CIj21Tg01_@j3<Tg015aj34Tg022[l<?Tg01b=j2ZTg023dj27Tg00;7j1UTg01`hj3TTg01aKj2QTg00<kj2OTg024dj1NTg01iSj8KTg01jUj2GTP0j3;Tg01kUj2FTg01m1j19Tg01moj8ETg00=Uj35Tg00R@j6DTg00E1j1ITg00EQj2JTg00Eoj1BTg00FMj1LTg00G[j2MTg00G8j2ATg00\Bj4=Tg00IDj1@Tg00_cj7RTg00]Qj8STg00Ifj2^Tg00JHj2]Tg00Jbj2\Tg00KNj3YTg00Kmj4WTg00M]j2XTg01nml?VTg00\mj7[Tf1R0g00ajR5g00bIR1P1g00biR8f0R9g00cIF[p=8g00`eR6#2R7#2R;1_66R3g0204R4g00f1R2#0R<#C#6R=%0<#0R>#0#0#0#6R?#>R@'PRA%6>#>#H\@R@g020kR>%23RB%2:R:g021aRCf;RDf<RE537g00`GRFA:66D'1A<66E,1Ff>RGf?RH547f=RIPEPDf:RJf9RKf8RLf7RMf6RNf5ROf4RPf3RQM<?f@RR/ZQp,1LRSp,2ar17JGPIfART%U<g01V[5T='Q,O?%NSPRPQGK1GRQA;3IQ1FPOp,3HIkfIRSO1fBR?,7GPTPRfGPOPM%9NGEPJPKPLPMPNPOPPPQf2R=P0p,2OKfJR<947SRUP<fC,7HP?PTfHR?P?PNPL%9MP9fKR?947<9379g01I7A57?0fLR?9370fMRH937=RVP9A57?=P7PHfO9379X>7PTPQP9EDW3P9O1P9XJVP9O1n200100000021000010000W3X>7A;7U<eg00gQRU#I%2U1J60%B6%L6RUP5P1P1P8P61M6Fg00ciR<1A62R2C=,8URV%@1PUP5P1P1P8PVP6P2P<P2C=,8UFRGS1^U8P9P=g00h=RUg00h]R8']1\9==5U8dAY6F0CWbObPbQX;6R811F911F01100'X[^;6RFP9A:66SPIO2b:P8PFP9A<66SPEO2b:M?VO:WNWFWEWDWCWBXABXR>XK@XMAPRPGPIPEPDPJPKPLPMPNPOPPM<?eWLWHWGWIX4CX@6X0BX7:X2:X6BX?>X8@X9AX=4X<3X57X1;PEPDPJPKPLPMPNPOPPPQP=P0P9O=W4X@6X0BX7:W2W6W?W8W9W=W<X57W1o"). Qed.

(* [comment removed for export] *)
Lemma credit_nonneg D LB FF LK cr A M V : ri_inv (HIk D) LB FF LK cr A M V -> 0 <= fst cr /\ 0 <= snd cr.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Fam"; "Derived"] "h01Hh11fh21bh31Ah41Dh52FFh62LBh72LKh81Mh91Vh:2crh;2RIh<1Wh=2W1h>2W2h?2_Hh@3_H0hA3_H1hB4_H10hC4_H11hD3_H2hE3_H3hF3_H4hG3_H5hH3_H6hI3_H7hJ3_H8hK3_H9p;1p;2p;8p;>p;3p;4p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0g01M?R1p4p710R2p8P0g002gR3p4p710R4p8P0P3p4p7210p8P0p1003Cp4p710R5p8P0g003dR6p4p710p8P0P6p4p7210p8P0p1004AR7p4p710R8p8P0P7p4p7210R7p8P0p1004Up4p710R9p8P0p10051p4p710R0p8g005JR:p605000R;P2p8P;P4p8P;P5p8P;p1006Hp4p710p8P;p1006mp4p710p8P;g007MR5p4p710p8P;p1007jR4p4p710p8P;P4p4p7210p8P;p1008>p4p710p8P;P0p8g008ZR0p4p710R;P8p8P;P7p8P;P9p8g00@Lj1PTg01^4j2{Tg008oj17Tg009Tj1bTg00:2j1_Tg00:Uj1rTg01moj8oTg025gj2lTg026ll>jTP1j3;Tg01cBj4zTg01fNj3ATg0281j3YTg029:j3BTg023dj2WTg01dFj3VTg01eIj3>Tg00;Uj2FTg02:@j1nTg00CIj21Tg01I7j2[Tg02;=R1j1kTg02<<j1iTg02=<j1hTg00M=j2RTg00;7j18Tg016Aj1JTg00E1j1gTg015aj3ETg02><j2KTg02?=j2eTg02@<j1dTg00kEj2cTg02A<j1yTg02B=j1xTg01H0j1wTg00M]R9j20Tg00jAj1vTg00=Uj3`Tg00<2j2uTP6j2tj3LTg00lBj4mTg01_@j3HTP5j3XTP3j4?TP0j2<Tf0R0#7#7p=Mg00`eR3?L30p=ZAH330p=ff1R5=X:0p=:f2R61050'0p==f4R;f3R71050,06'0'0p=3g00`GR89`30p=QAA765/00p=I%70#7#7#7p=9g02C>R49B50p=D%J0#Jp=CAL337,18AH336,18AA504'0'0p=2f6R2f5R<P3P;P7C?,<3P:P3P1AX:65C?,<3/00'0'0p=4AB<;71050,06'0p=6AB654/00p=GAL335,18AH330,18'0p=5P:P3P1P0C?p=sAH336,18AA504'0p=U1<361185/00'0p=qP7P3P6P5C?,<3/00,0;p=pP6P3P5P0C?,<3p=OP:P3P1AX:<;C?,<3AL337,18AH336,18AA504'0'0'0p=@P6P3P5P0C?p=N1<35/00,06,07p=^1<35/00p=]P:P3P1P0C?,<3p=aAL330,18p=SAH330,18p=TAA504p=\%P3#PR11{33R=#PR>%P:R?g02D>R@g00f1RA#7RB#7RC#7RD#7RE#MRF#b#_%bD#_#r[RDg02E;RGp,3HIkRHf7RIO1P2P<P;P7P6P5P0Gop,1LRJp,2arRKp,1Cp,4scfgPHf8RHO1p,2OK/lHPIP2P<P;P7P6P5P0M>jA;=0HPJPK%Z5RL%f5RMCzRNAA;LMAY;LMAB<LMf9RO,WL9VLM1:HI9>LM1FLM%nKRP'11FP4RQ/1L'[RR3=D3[^2=A;:0I%k5RS,1PRT%i5RU#hRV,FS/1QRW1RSV#QRX%8A%8BRY%JARA#8%8C%JBRB#8%g35E35E35E35E35E39E389;3URUP;PSPV1KSH/:I9>SVCID3[^1:1eP4R4%dKR8%MF#9RF#7#M#9#9#8RC'cRZ,1QR[%yJ,1Q%xJ/1P'[RJ1D7PP7PZ1c8ZRQ%wKR\%8FRF'F,1Z1FZF,1\'0R]1R\F#Q%vKRK1F\C5`3%CA#C#C#C#C#C#C#7#M#9#9#9#9#9#9#9#8/18%JB#C#8,uYRY,18'0%8E,R8#Q'03=R811KYRYP=1t33R3PIP2P<P;P;P6PPC2F4E63=D3P9A;=0OPNAA<LMAY<LMAB2LMf:RK,WL9VLM1:OH9>LM;=RD3[^2=A;:0HPTPWPXPUP<PSPV1KSO/:H9>SVCID3[^1:P4P[PJP;PZPQP]P8PYP=P3PHPIP2P<P<P7PPC2F4E69G;PD31522P0f;RE9;=0PNAAILMAYILMABHLMf<RN,WL9VLM1:EKRB9>LM;=RD3[^2=A;:0EPTPWPXPUPHPSPV1KSN/:E9>SVCID3[^1:P4P[PJPIPZPQP]P8PYP=P3PEPKPOPHPHP2PPC2F4E69GIPD3P9A;:0NPTPWPXPUPOPSPVf=RR,KS/:N9>SVCID3[^1:P4P[PJ1DHPPHPZPQP]P8PYP=P3PN%sB%ZOAUOIP3qDpE6D315KKP0f>RO9;:0PTPWPXPUPEPSPVf?RU,KS/:O9>SVCID3[^1:P4P[PJ1DEPPEPZPQP]P8PYP=P3PUPOPRPNPNPKPPC2F4E6D3P9P4PNPZPQP]P8PYP=P3f@RKPUPOPRPRPEPPC2F4E69GNP9=[J15OOP0PUPZPQP]P8PYP=P3fCRNfBREfARRPKPKPOPPC2F4E69GUP9=[JP9P[1DKPPKPZPQP]P8PYP=P3fDRKPNPEPRPRPUPPC2F4E65=J15EEP01DNPPNPZPQP]P8PYP=P3fGRUfFRRfEROPKPKPEPPC2F4E65=JP9PJPKPZPQP]P8PYP=P3fHREPUPRPOPOPNPPC2F4E69GKP15RRP0PUPZPQP]P8PYP=P3fKRKfJRNfIROPEPEPRPPC2F4E69GUPP91DEPPEPZPQP]P8PYP=P3fLREPKPNPOPOPUPPC2F4E615NNP01DNPPKPZPQP]P8PYP=P3fORUfNROfMRRPEPEPNPPC2F4E6P9ABEZQP]P8PYfPRE9O=3PUPOPRPRPKPPE@D315OOP0ABOZQP]P8PYfSRQ9O=3fRRZfQRKPEPEPOPPE@D3P9P]P8PYfTRO9N=3PQPZPKPKPUPPE@C^15ZZP0P8PYfWRU9N=3fVRKfUREPOPOPZPPE@C^P9P8PYP=P3fXRZPUPKPEPEPQPPC2F415KKP0PYP=P3f[RQfZREfYROPZPZPKPPC2F4P9PYf\RK9N=3PQPEPOPOPUPPE@']15EEP0f_RU9N=3f^ROf]RZPKPKPEPPE@']P9f`RE9O=3PUPOPZPZPQPPE@15OOP0fbRQ9O=3PQfaR3PEPEPOPPE@P9fcRO/:Q#aP3P3PUPPC215QQP0feRUfdR3':#aP3P3PQPPC2P9%SUAUUOPffRU/5UP0fgRO#Sfh?UUPP9fi#T1\OPfjRO/5OP0fk#T1\OPfmRO#S%TOP<P5CmWCW>P5P0O2n2001000000120000000W0W=P5P0O2n2001000000120000000W0WBP5P0O2n2001000000120000000W0WKP5P0O2n2001000000121000000W0XJYP5P0O2n2001000000121000000W0XI8P5P0O2n2001000000121000000W0XH]P5P0O2n2011000000121000000W0WGP5P0O2n2011000000121000000W0WFP5P0O2n2011000000121000000W0XEJP5P0O2n2011000000121000000W0XD[P5P0O2n2011000000121000000W0XA4P5P0O2n2011000000121000000W0W@P5P0O2n2011000000121000000W0W?P5P0O2n2011000000121000000b<W;X9GX8DX3>X:@X7?X5?X6>X41PIP2P<P;P7P6P5P0O8W9W8X3>W:X7?W5W6W4o"). Qed.

Theorem amallocU_holds : amallocU_spec.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Fam"; "Derived"] "p'0h02CRh14POSTh21Wh34__x1h47__arithh54__ffh68__varmaph75__with81ah91Ah:2C1h;2C2h<1Dh=2FFh>1Hh?3Hinh@2HnhA2HrhB1KhC2KthD2LBhE2LKhF1MhG3PREhH1RhI2RIhJ2UKhK2_HhL1bi001bhM2crhN2fxhO5modelhP1np;1p;2p;<p;4p;3p;5p;8p;9p;Ap;Dp;Cp;7p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0g01M?R1p4p710R2p8P0p1002gR3p4p710R4p8P0P3p4p7210p8P0p1003Cp4p710R3p8P0g003dR5p4p710p8P0P5p4p7210p8P0p1004AR6p4p710R7p8P0P6p4p7210R6p8P0p1004Up4p710R8p8P0p10051p4p710R0p8g005JR9p605000R:P2p8P:P4p8P:P3p8P:p1006Hp4p710p8P:p1006mp4p710p8P:p1007Mp4p710p8P:p1007jR3p4p710p8P:P3p4p7210p8P:p1008>p4p710p8P:P0p8p1008Zp4p710R0P7p8P0P6p8P0P8p8g00@Lj1;Tg008oj16Tg016Aj1_Tg009Tj1HTg00:2j1WTg01^Tj2jTg00:Uj1TTg01^4j2^Tg02F6l<OTg00<Oj2ZTg00CIj20Tg00M]R8j29Tg02G@j1XTg02HKj4uTg01Zij38Tg00;7j1>Tg02IPj3ETg015aj3GTg00kEj2:Tg02JRj3ITg01_]l<@Tg00JHj2PTg00=Uj32Tg00=oj1\Tg02KPj1[Tg00@lj2=Tg02LQj5<Tg02MOj4YTP1j3BTg01m1j1CTg01moj8LTg02NZj1KTg00IDj1QTg01kUj2JTg01`hj3ATg01aKj25Tg02OQj1tTg02PNj1VTg01hNj1sTg00<kj2UTg02QGj5MTg00E1j1NTg02RHl9rTg00EQj2qTg00Eoj1iTg00FMj1hTg00G[j2STg00G8j2fTg01<:j3dTg00Ifj2eTg00Jbj2cTg00KNj3bTg00Kmj4gTg02SSlAaTg02TdlDkTg02UllClTP5j3`Tg01_@j3mTg01lQj4nTg00\Bj4]Tg00\mj7oTg00]Qj8pTg00`eR5f0R17`5p=1Am551p=4P5P5f1R0P1Cnp=?f2R61901'9p=7g00`GR7/01p=3P5P0g00ciP1C]p=FP0g00ajR:g00bIR3P3g00biR4P1g00cIFop=Df3R2P:P3P3P4P6P0P1Gpp=R%;5R:#;g0204g00f1R;#6R<#_R=#HR>%6<R?#6R@#6#6#6#HRA#WRB'j%H@#W#T\Bg020k1^55#;R@%;9R9g02D>RCg021af<RDf;REf:RFf9RGf8RHf7RIf6RJf5RKf4RLP2P6P0M<O1Z72g02W4,02'9p,3LR_#XPDPEP6Cug00h=RMp-0RNf?RO=82K%>;RP%1I'0p,1LRQ?EIKn0100000020000f@RR9G:LPMPCA8LRJ%1H/:P%4H'?AIQHJn0100000020000POf>RLf=RSPDPEPFPGPIPJPKM<@fART=8KIPM1PM1fBRK=8JH=2M1PMfDRJ=8HF=2M1PMPNP0%1SRN,0PAEQSEn0100000020000fFRU9G:FPMPCP6%1L/:P%4L'?AIQLDn0100000020000fERCPJfCRVPKPTPRPOPSPDPEM<@g02X6RW%\QRXp,4scfgRYp,6cfg_atRZPUPC%[Q,=AR[PJPVO5PDD<]1]0]2P0A8IVGR\g00h]R]52M%1D,0PAG:GCR^1:NP%4S'?PJPVPKPTPRPOPLPDPEPFM<@PFPUPDP6CYAB:FUg01[nRN/0Dg01]1R_,0D37P8fGR`9B:E10NS10S_'9PWPXPYPZP`PUP[PCPJO5PSD<P1fIRa9B:S10NR10R_'9PLfKR_fJRNPafHRbP`PUPCPJPVPKPTPRM<OP8p,3HIkRcfLRdO1P`PUPCPJPVPa%CbGL%TBRe%Kb%QBRf321JVb%6=#>g01V[R=5A>Rg,5N1=AK52B%>?=A>=R?,5N%tQ,=ARh52BAA>P=Ri,5N#VPQp,2arRjPa%sQRk%><=A>=R=,5N,UADMPTg02Xl#NR>O1373737PWPXPYPZPdP_P[PNPaO5PKD<P1PcfNRcO1PaPbP`PUPCP_%CNGL%K_=2ef1JU_fMRf/5g1=AC52B15f?=2Bh15fi#VPQPjPdPk15f=,UADMPJP>O1373737fPR>P_PNPaPbP`Pf%CdP0M9r%1b#3%4b#3'9P8%1a#3%4a#3PWPXPYPZfQRZP>P[fOR[PcO5P`D<P1%1_#3%4d#3p,2OKR`fURYfTRXfSRWfRR8PZP>P[PcPfPdP_PNPaPbPFPRPUPEPYPa%1f/:P%4f'?RfPXPWP8PZP>P[PcPdP_PNPEg00gQRN#NR_%;NRN1q50Rd%i5R[%h5R>1S5PRZ1f5;R;'F,D>%Q3R31S57R8Ad5;Z'F,D>CR1e>4R4P1P61PM]1c16=2M]dAb570CgR7b5b6b7X3510P11:0P#3[^35P1%1cPTO2b4%1f#3eP_PNPdP[P>1F8;,D>R>P3P>CRP4P7b5b6b7X35%31%30[^35P1%4cP0O2b4%4f#3ePOMAaMDkW;W:P0P1O2n2001000000121000000b8WKWIP0P1O2n2001000000121000000b>WAW?P0P1O2n2001000000121000000b8W1W0W2g01SZ92M\AEQDFP^AIQSEPJPVPKPTPRPOPLPDPEPFM<@P`PUPCPJPVPKPTPRPOPLPSPDPEPFPGPHP0PIP1MClW1W0W2n0110000020100P1P2P6O3b2bLW1W0WJW@WGXC:WBXP5X9@WMXE9W=WDWOWFWHWNW<g02Ybeo"). Qed.
Theorem afreeU_holds : afreeU_spec.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIfaceAMr ()) ["Fam"; "Derived"] "p'0h04POSTh11Wh24__x1h37__arithh44__ffh58__varmaph65__with71ah81Ah92C1h:2C2h;1Dh<2FFh=1Hh>3Hinh?2Hrh@1KhA2KthB2LBhC2LKhD1MhE3PREhF1RhG2RIhH2UKhI2_HhJ1bi001bhK2crhL2fxhM5modelhN1nhO1up;1p;2p;=p;4p;3p;<p;5p;8p;9p;Ap;Dp;Bp;7p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0g01M?R1p4p710R2p8P0p1002gR3p4p710R4p8P0P3p4p7210p8P0p1003Cp4p710R3p8P0g003dR5p4p710p8P0P5p4p7210p8P0p1004AR6p4p710R7p8P0P6p4p7210R6p8P0p1004Up4p710R8p8P0p10051p4p710R0p8g005JR9p605000R:P2p8P:P4p8P:P3p8P:p1006Hp4p710p8P:p1006mp4p710p8P:p1007Mp4p710p8P:p1007jR3p4p710p8P:P3p4p7210p8P:p1008>p4p710p8P:P0p8p1008Zp4p710R0P7p8P0P6p8P0P8p8g00@Lj1<Tg008oj18Tg016Aj1]Tg009Tj1DTg00:2j1RTg01^Tj2hTg00:Uj1STg01^4j2\Tg02Zml=KTg02\5j1YTg02HKj4XTg015aj3ETg01Zij3=Tg00;7j1@Tg00;Uj2;Tg022[l<ATg00JHj2OTg00=Uj31Tg00=oj1^Tg02]>j1[Tg00@lj2?Tg02LQj5>Tg02MOj4ZTP1j3:Tg00CIj27Tg00M]R1j26Tg01m1j1CTg01moj8ITg02NZj1HTg00IDj1MTg01kUj2GTg01`hj3BTg01aKj24Tg02OQj1WTg02PNj1FTg024dj1VTg00<kj2UTg02QGj5TTg00E1j1JTg02RHl9qTg00EQj2pTg00Eoj1oTg00FMj1nTg00G[j2QTg00G8j2gTg00\Bj4PTg00H>j3fTg00Ifj2eTg00Jbj2bTg00KNj3cTg00Kmj4dTg02^=lAaTg02_LlD`Tg02`RlBiTP5j3_Tg01_@j3jTg01lQj4kTg00\mj7lTg00]Qj8mTg00`eR5f0R87_5p=2Aj558p=3P5P5f1R0P8Ckp=9f2R61608'6p=5g00`GR7/78p=0P0g00ajR:g00bIR3P3g00biR4P8g00cIFlp=Lf3R2P:P3P3P4P6P0P8Gmp=N%<5R:#<g0204g00f1R;#8R<#]R=#DR>%8<R?#8R@#8#8#8#DRA#RRB'h%D@#R#S\Bg020k1\55R@#<RC%<9R9g02D>RDg021af=REf<RFf;RGf:RHf9RIf8RJf7RKf6RLf5RMf4RNP2P6P0M=Kp,3LR_#YPFPGP0CXf?RO9E:6g00h=RPPDA=6ON%2K%@;RQ';%3K'9PKn0100000020000f>RRPEPFPGPHPIPJPLPMP2M<Af@RS==2MPP1OP8fAR2==NL=1P8PPfCRN==LJ=1P8fDRT9E:KPPPDP0%2F/;Q%3F'9PFn0100000020000PNfBRDP2PSPOPRPEPGPHPJM<Ag02X6RUp,1LRV#^RWp,4scfgRXp,6cfg_atRYPTPN%[V,?ARZPDP2O5PID>]0]1P0A=MDKR[g00h]R\51PAE:LNR]%2G/;Q%3G'9PDP2PSPOPRPEPFPHPIPKM<APKPTPIP0CZA::KTg01[nR^/7Ig01]1R_,7I35P1fER`9::J17^H17H_'6PUPWPXPYP`PTPZPNPDO5PHD>P8fGRa9::H17^E17E_'6PGfIR_fHR^PafFRbP`PTPNPDP2PSPOPRPEM=KP1p,3HIkRcfJRdO1P`PTPNPDP2Pa%CbGI%SBRe%Hb%MBRf311G2b19SO=:@`%8=#@g01V[R=5B>Rg,4^1?AS51B%@?=B>=R?,4^%WV,?ARh51BAB>Q=Ri,4^#FPVp,2arRjPa%VVRk%@<=B>=R=,4^,UADTPRg02Xl#JR>O1'6353535PUPWPXPYPdP_PZP^PaO5POD>P8PcfLRcO1PaPbP`PTPNP_%C^GI%H_=1ef1GT_19ND=:@^fKR@/4g1?AN51B14@?=1Bh14@i#FPVPjPdPk14@=,UADTP2P>O1'6353535fNR>P_P^PaPbP`P@%CdP0M9q%2b#0%3b#0'6P1%2a#0%3a#0PUPWPXPYfORYP>PZfMRZPcO5PTD>P8%2_#0%3d#0p,2OKRXfSRWfRRUfQR1fPRAPYP>PZPcP@PdP_P^PaPbP`PHPTPGPWPb%2@/;Q%3@'9R@PUP1PAPYP>PZPcPdP_PaPGg00gQRa#JR_%<aRa1p50Rd%o5RZ%n5R>P51Q57RYg00ciRA1g5;R;CP,L>R1%M3R3P5PYPA1Q5Q9f5;CP,L>CN1e>4R4P8P61OP\1b86=1P\dAc570CdR7b4b5b6X25%08R\1;0Q#0[^25P8%2cP6O2b3%2@#0eP_PaPdPZP>P1P3P1CNP4P7b4b5b6X25%00\\^25P8%3cP0O2b3%3@#0ePOMAaMD`W:W9P0P8O2n2001000000121000000b7WIWGP0P8O2n2001000000121000000b=W?W>P0P8O2n2001000000121000000b7W0W1g01SZ91P[P]PGPDP2PSPOPRPEPFPHPIPKM<APXPTPNPDP2PSPOPRPEPFPGPHPIPJPKPLPMP8MBiW0W1n0110000020100P8P6O2b1bJW0WHWEXA:W@XN5XO5X8CWKXC9W<WBWMWDWFWLW;g02aXeo"). Qed.
End Derived.
End Fam.

End HAR.

End HeapIfaceAMr.
Module IcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record icpt_layout : Type := ICL {
  icl_strlen : Z;                    (* [comment removed for export] *)
  icl_scr_strlen : Z;                (* [comment removed for export] *)
  icl_ro_lo : Z; icl_ro_hi : Z;      (* [comment removed for export] *)
  icl_globals : list (Z * Z);        (* [comment removed for export] *)
  icl_poison : list (Z * Z);         (* [comment removed for export] *)
  (* [comment removed for export] *)
  icl_memcpy : Z;                    (* [comment removed for export] *)
  icl_memmove : Z;                   (* [comment removed for export] *)
  icl_ctxslot : Z;                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  icl_strerror_r : Z;                (* [comment removed for export] *)
  icl_scr_strerror : Z;              (* [comment removed for export] *)
  icl_strerror_cells : list (Z * Z * Z);  (* [comment removed for export] *)
  (* [comment removed for export] *)
  icl_sro_lo : Z; icl_sro_hi : Z
}.

(* [comment removed for export] *)
Definition EINVAL_MSG : list Z := [73; 110; 118; 97; 108; 105; 100; 32; 97; 114; 103; 117; 109; 101; 110; 116; 0].

Section IIface.
Variable L : asan_layout.
Variable ar : asan_run.
Variable IL : icpt_layout.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

(* [comment removed for export] *)
Definition astrlen_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (s K : Z) (buf : list byte) (Kt : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 s ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (icl_scr_strlen IL) sp ->
    0 <= s -> s + Z.of_nat (length buf) <= 2 ^ 47 -> 0 <= K < 2 ^ 27 ->
    rdn (hl_segs L) M (Z_to_bv 64 s) (length buf) = Some buf ->
    (s + K) / 8 * 8 + 8 <= s + Z.of_nat (length buf) ->
    nth (Z.to_nat K) buf (Z_to_bv 8 0) = Z_to_bv 8 0 ->
    (forall j, (j < Z.to_nat K)%nat -> nth j buf (Z_to_bv 8 0) <> Z_to_bv 8 0) ->
    (forall i, 0 <= i < Z.of_nat (length buf) ->
               hl_img_lo L <= s + i < hl_img_hi L \/ aclient L ar LB FF sp (icl_scr_strlen IL) (s + i)) ->
    (forall a, icl_ro_lo IL <= a < icl_ro_hi IL -> M (Z_to_bv 64 a) = None) ->
    aacc M s (K + 1) -> app_rng ar s (K + 1) ->                              (* [comment removed for export] *)
    Kt [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        getr R' 10%bv = Z_to_bv 64 K -> regs_preserved R R' ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp (icl_scr_strlen IL) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - icl_scr_strlen IL <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') Kt) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (icl_strlen IL)) M model) Kt.

(* [comment removed for export] *)
Definition rt_globals : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    Forall (fun g => shadow_blk M (fst g) (snd g) /\ shadow_allowed A (fst g) (snd g)) (icl_globals IL).

(* [comment removed for export] *)
Definition rt_img_shadow : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    forall a n, hl_img_lo L <= a -> a + n <= hl_img_hi L -> 0 < n -> Forall (fun r => a + n <= fst r \/ snd r <= a) (icl_poison IL) ->
      (forall x, in_shadow_of a n x -> byte_at M x 0) /\ shadow_allowed A a n.

(* [comment removed for export] *)
Definition LOWSH_LO : Z := 0x7fff8000.      Definition LOWSH_HI : Z := 0x8fff7000.
Definition HIGHSH_LO : Z := 0x2008fff7000.  Definition HIGHSH_HI : Z := 0x10007fff8000.
Definition rt_shadow_defined : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    forall x, (LOWSH_LO <= x < LOWSH_HI \/ HIGHSH_LO <= x < HIGHSH_HI) -> M (Z_to_bv 64 x) <> None.

(* [comment removed for export] *)
Definition rt_tls : Prop :=
  forall LB FF LK cr A M model, ri_inv HI LB FF LK cr A M (vml_of model) ->
    exists ctx th tbv tev blk : Z,
      cell_is (hl_segs L) M (icl_ctxslot IL) 8 ctx /\ cell_is (hl_segs L) M (ctx + 152) 8 th /\
      cell_is (hl_segs L) M (th + 48) 8 tbv /\ cell_is (hl_segs L) M (th + 56) 8 tev /\
      cell_is (hl_segs L) M (hl_tp L + 8) 8 blk /\ cell_is (hl_segs L) M (blk + 24) 8 (hl_tp L) /\
      4096 <= ctx /\ ctx + 160 <= ahl_ceil ar /\ 4096 <= th /\ th + 64 <= ahl_ceil ar /\ 4096 <= blk /\ blk + 4096 <= ahl_ceil ar /\
      0 <= tbv < 2 ^ 64 /\ 0 <= tev < 2 ^ 64 /\
      (ctx + 160 <= hl_img_lo L \/ hl_img_hi L <= ctx) /\ (th + 64 <= hl_img_lo L \/ hl_img_hi L <= th) /\ (blk + 4096 <= hl_img_lo L \/ hl_img_hi L <= blk) /\
      (* [comment removed for export] *)
      (ctx + 160 <= th \/ th + 64 <= ctx) /\ (ctx + 160 <= blk \/ blk + 4096 <= ctx) /\ (th + 64 <= blk \/ blk + 4096 <= th) /\
      (forall a, ctx <= a < ctx + 160 \/ th <= a < th + 64 \/ blk <= a < blk + 4096 ->
                 (forall sp scr, ~ aclient L ar LB FF sp scr a) /\
                 page_in_ranges (page_base (Z_to_bv 64 a)) (m_vm_lazy model) = false).

(* [comment removed for export] *)
Definition amemcpy_libc_spec : Prop := amemcpy_spec_at L ar scfg HI (icl_memcpy IL) false.
Definition amemmove_libc_spec : Prop := amemcpy_spec_at L ar scfg HI (icl_memmove IL) false.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition astrerror_r22_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (Kt : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 22 -> getr R 11%bv = Z_to_bv 64 (sp + 16) -> getr R 12%bv = Z_to_bv 64 1024 ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (icl_scr_strerror IL) sp ->
    sp + 128 <= ar_sptop ar ->
    app_rng ar (sp + 16) 17 ->
    (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= 17 -> store_ok (hl_segs L) M (Z_to_bv 64 (sp + 16 + d)) m = true) ->     (* [comment removed for export] *)
    (forall x, in_shadow_of (sp - 64) 192 x -> byte_at M x 0) ->                                                          (* [comment removed for export] *)
    Forall (fun c => cell_is (hl_segs L) M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) (icl_strerror_cells IL) ->
    (forall a, icl_sro_lo IL <= a < icl_sro_hi IL -> M (Z_to_bv 64 a) = None) ->                                          (* [comment removed for export] *)
    Kt [] ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),                              (* [comment removed for export] *)
        getr R' 10%bv = Z_to_bv 64 0 -> regs_preserved R R' ->
        rdn (hl_segs L) M' (Z_to_bv 64 (sp + 16)) 17 = Some (map (Z_to_bv 8) EINVAL_MSG) ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp (icl_scr_strerror IL) a -> ~ (sp + 16 <= a < sp + 33) ->
                   M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - icl_scr_strerror IL <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx' R' (getr R 1%bv) M' model') Kt) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (icl_strerror_r IL)) M model) Kt.

Record aicpt_ok : Prop := AICOK {
  aic_strlen : astrlen_spec;
  aic_globals : rt_globals;
  aic_img_shadow : rt_img_shadow;
  aic_shadow_defined : rt_shadow_defined;
  aic_tls : rt_tls;                          (* [comment removed for export] *)
  aic_memcpy_libc : amemcpy_libc_spec;       (* [comment removed for export] *)
  aic_memmove_libc : amemmove_libc_spec      (* [comment removed for export] *)
  (* [comment removed for export] *)
}.
End IIface.

(* [comment removed for export] *)
Record as0_icpt_layout (IL : icpt_layout) : Prop := AICL {
  aicl_strlen : icl_strlen IL = 0x6a294;
  aicl_scr_strlen : icl_scr_strlen IL = 2304;
  aicl_ro_lo : icl_ro_lo IL = 0x103d0; aicl_ro_hi : icl_ro_hi IL = 0x103f0;
  aicl_globals : icl_globals IL = [(0x23a40, 7); (0x23a60, 53); (0x23ae0, 13); (0x23b00, 39); (0x23b60, 6); (0x23b80, 21); (0x23c20, 6); (0x23c40, 6); (0x23c60, 5496); (0x25720, 2748); (0x26480, 11); (0x264a0, 74); (0x26520, 6); (0x26540, 11); (0x26560, 5); (0x26580, 5); (0x265a0, 6); (0x26660, 1); (0x267e0, 17); (0x26820, 23); (0x26860, 13); (0x26880, 38); (0x268e0, 42); (0x26940, 43); (0x269a0, 59); (0x26a00, 58); (0x26a60, 43); (0x26ac0, 77); (0x26b40, 18); (0x26b80, 22); (0x26bc0, 33); (0x26c20, 45); (0x26c80, 60); (0x26ce0, 42); (0x26d40, 37); (0x26da0, 51); (0x26e00, 13); (0x26f40, 3); (0x26f60, 10); (0x26f80, 13); (0x26fa0, 14); (0x27020, 54); (0x27080, 440); (0x151520, 88)];
  aicl_poison : icl_poison IL = [(0x23a40, 0x272a0); (0x151520, 0x1515a0); (0x15b8a0, 0x15c3a0)];
  aicl_memcpy : icl_memcpy IL = 0x7ebb8;        (* [comment removed for export] *)
  aicl_memmove : icl_memmove IL = 0x7ebb4;      (* [comment removed for export] *)
  aicl_ctxslot : icl_ctxslot IL = 0x6b4fb8;     (* [comment removed for export] *)
  aicl_strerror_r : icl_strerror_r IL = 0x6a30c;                                                         (* [comment removed for export] *)
  aicl_scr_strerror : icl_scr_strerror IL = 4320;                                                        (* [comment removed for export] *)
  aicl_strerror_cells : icl_strerror_cells IL = [(0x693ad0, 8, 0x6b3dc8); (0x6b3df0, 8, 0)];             (* [comment removed for export] *)
  aicl_sro_lo : icl_sro_lo IL = 0x10000; aicl_sro_hi : icl_sro_hi IL = 0x158000                            (* [comment removed for export] *)
}.

End IcptIfaceA.
From Stdlib Require ZArith List Lia.
Module ShadowRLawsB.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_ShadowRLawsB () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C46Stdlib5Lists4List4inclc59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C45stdpp;list_basics4list;list_filterC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appC35stdpp4base6FilterC46Stdlib5Lists4List7existsbI35stdpp4base5NoDup00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z9div_smallC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z>div_unique_posC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9div_add_lK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib7Mh_0089<ShadowRLawsB:shadow_tbyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA:shadow_blkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA1SC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA7byte_atC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z7div_posK47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ:ann_shadowC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib7Mh_0089<ShadowRLawsB>shadow_blk_tbyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089<ShadowRLawsB7div8_upC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6eq_decK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega3Op204C56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundc59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib7Mh_0089<ShadowRLawsB=shadow_tby_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0089<ShadowRLawsB?shadow_blkR_tbyC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma div8_up (m : Z) : 0 <= m -> (m mod 8 = 0 -> (m + 7) / 8 = m / 8) /\ (m mod 8 <> 0 -> (m + 7) / 8 = m / 8 + 1).
Proof.
ltac2:(KReplay.run1 (kr_t_ShadowRLawsB ()) [] "h04__x1h11Hh22H0h32H1h42H2h52H3h67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<2H4h=2H5h>5heq_qh?5heq_rh@2q0hA2r0hB1zhC2HrhD4__x2hE4__x3hF1mhG1qhH1rhI1DhJ1EhK2HmhL1Rp%0p;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp4p70R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj1UTg009Tj1TTg00:2j1]Tg00:Rj1yTg00;2j1lTg00;Pj1fTg00;nj1bTg00<Yj2GTg00=<j2\Tg00=^j2ZTg00>8j2vTg00>dj3@Tg00?>j3kTg00?]j4iTg00@Oj3ej2ETg00A0j22Tg00AMj23Tg00Amj3ATg00B^j3KTg00COj1LTg00Chj2Hj3[Tg00DOj26Tg00Dkj2DTg00ERj2=Tg00EnR6j2<Tg00FIj2CTg00Foj2BTg00GUj1VTg00H:j21Tg00HWj1xTg00I5j2wTg00IVj1uTg00J5j2YTg00J^j3tTg00KGj3qTg00L0j2pTg00L\j3oTg00M<j2RTg00MZj4jTg00N8j2NTg00N[j3QTg00O>j1hTg00O`j2PTg00P=j3gTg00P`j6MTg00Q>j2FTg00Q[j3dTg00R>j6cTg00Rfj6mTg00SBj4nTg00S]j4aTg00T@j4STg00Tkj7`Tg00UOj6_Tg00V3j3rTg00VVj8sTg00W:j7^Tg00W^R0f0R4'=p=4g00X<R5f1R7g00XZP4CSp=;P7g00YAR2g00Y`R3P3g00Z@R1P4g00Z`F`p=5P7P2P3P3P1P4E_p=WA@540p=8f3R8f2R9/P7/145@5p=91=091674'<p=7A@574p=0P5P7g00[@P4CSp=J1Z54p=?Ar574p=:P8P2P3P3P1P9P7P4Gsp=>11749@59p=IP5P7g00[gP4CSp=OP9P2P3P3P1P7P4F^p=X%44g00\NR2#UR:#U#U#TR;g00]3R<#]R=%y<R>%l5R?%f5R@%b5RA1G5;RB1G50RC';,5A'W1\A1R1P4P9g00]_RDg00^?RE'Z1v49=@DEdAk507CiREb7b:b;%8;RDg00^_S00[P4b6S015e7P7P;127;RF137;C9AA9;7%4;RG138;#4[AK8;9f4RH/2;#4\G1EH;%LDRIf5RJP;12J;13J;RKC9[1HJ;160;RLf6RM/3;RN?7N;[1DM;16;0ROf7RP/3;RQ,6;1=Q0'<[1CP;f8RR/2;RS#8\D1BR;f9RT/3;S02/0T\D12T;RUP5f:RV/3;RWP5P=P>P?P@1JCB,5AP1PEb7b:b;PLP4b6bHbGb5b4b3b2b1b8b99[9;139;R??7?;128;P513H;P5%?K104KRKePK12M;RK#?109KRKePKAAP;M13R;#4\GAKR;P%4U\G1ET;PVP;12V;S03PWC9\I1HV;f;RU/3;RK?7K;\L1DU;f<R?/3;RX,6;1=X0'<\O1C?;f=RY/2;#8\D1BY;f>RZ/3;R[/0Z\D12Z;S04P5f?R\/3;S05P5P6%4U16U;fAR]%V2R^#V#TR_'1PYP;11?_C9PY%4YR`16Z;%x2,w5g00_<Ra#u,Y55t51Y5a5q5g00_['p=o<=P>P51R59P71R58CjP@PA1N52R<1N5:R:9Q5B1N5^R^':';,5A%h3R31G5_Ra,:<RbAQ5:B1:^a':';,5AC>P1PEb7b:b;X05XD5XE5P4P;P7P9C9117_Ra1P9;R^118_3I[^05^D5^E5P4f@R:P]fEfCRcO4b6W=W<P7P4O2n2001000000121000000bAb@b5b4b3b2b1b8b9b>b?11J_P7P;114_RJC9P511^aR^%89Rd10FH[%LdRe%T2R2,1HRf,0F['<XB5P512a;,19107H\d107f\e'<XB5%87Re119_Rd/2;RF,18Rg/08[%LeRhAIg82[P5P011H4Rg/0HXB5%?Q109QRQeRiPQ%?S10HSRSeRHPSAAT;RRj%4W\GRWAKV;TRk12U;S06#4\GRl1EU;RmP?P;12?;PXC9\IRn1H?;Ro13Y;Rp?7p;\LRq1DY;Rr16;[1=[0'<\OR[1CZ;Rs12\;S07#8\DRt1B\;Ru13:;S08/0:\DRv12:;RwP513];R]P5P6P`16Y;Rx11\0/0\P\%4\Ry16:;RzP=P>1R57R{P@1:<C/;<,5AP1PEb7b:b;X051140/04^05P4PcO1S09b6W=W<P7P4O2n2001000000120000000bAb@b5b4b3b2b1b8b9b>b?PFPiPQPHPSPjPWPkPlPmPnPoPqPrP[PsPtPuPvPwP5P]P5P6P`Px11Z_Rc?7c;P\P=P>P{P@PA1;<C,5AR|P3PA1OC<,5AS0:P31OCb,5A1JbB,5A5XAC>C>P1PEb7b:b;X05%84R}%47A7dd;[[^05P4fBR~P:P9O3b6X=zX<yP7P4O2n2001000000120000000bAb@b5b4b3b2b1b8b9b>b?9gd;EMXCeP5P210gfXB5PiPQPHPSPjPWPkPlPmPnPoPqPrP[PsPtPuPvPwP5P]P5P6P`Px11\2Rg/0gP\P=P>P{P@1G52Rg,:<Rf/;f,5AP1PEb7b:b;X051142Rf/0f^05Q09b6X=zX<yP7P4O2n2001000000120000000bAb@b5b4b3b2b1b8b9b>b?PFPdP;P21F92PiPQPHPSPjPWPkPlPmPnPoPqPrP[PsPtPuPvPwP5P]P5P6P`Px1FZ2Rd?7d;P\P=P>P{P@PA1WA|P3PA1J<B,5AP3PAQ0:P3Ad5<gR<,OC,5A1J<B,5A5XAC>C>C>P1PEb7b:b;X05Q00\}167;%491F82R}?7};[[[^05P4P~P:P7P9O4b6X=zX<yP7P4O2n2001000000121000000bAb@b5b4b3b2b1b8b9b>b?PiPQPHPSPjPWPkPlPmPnPoPqPrP[PsPtPuPvPwP5P]P5P6P`Px1P;2Rx=IcdP\P=P>P{P@AQ5Bg/:<,;b,5AP1PEb7b:b;X051F429IJx^05P4P~O1b6X=zX<yP7P4O2n2001000000120000000bAb@b5b4b3b2b1b8b9b>b?EcEmXChCn12^;P9P;Pa%?N107NRNePN12P;RN#?108NRNePNAAR;PQ02#4\GAKT;RQ03#4\G1EV;PUP;Q06PKC9\I1HU;A7XX;\L1D?;16;p1=p0'<\O1CY;Q04#8\D1BZ;Q05/0\\DQ07P5Q08P5P6%4?16?;PIPZ%4Z16\;Q01W=W<P7P4O2n2001000000120000000bAb@b5b4b3b2b1b8b9b>b?CaEM11M_P4EMbJbHbGbLbIWKXF5P4O1XF5o"). Qed.

Section Laws.
Variables M M' : word -> option byte.

(* [comment removed for export] *)
Definition shadow_tby (u n : Z) : Prop :=
  forall j, 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S u + j) v -> byte_at M' (HeapIfaceA.S u + j) v.

Lemma shadow_blk_tby u n : 0 < n -> shadow_tby u n -> shadow_blk M u n -> shadow_blk M' u n.
Proof.
ltac2:(KReplay.run1 (kr_t_ShadowRLawsB ()) ["Laws"] "h04__x1h11Hh22H0h32H1h42H2h52H3h67__arithh74__ffh86__sat1h96__sat2h:8__varmaph;5__with<1qh=1rh>2P0h?2H4h@2H5hA4__x2hB1nhC1uhD2HjhE2HmhF2HnhG3TBYhH2Z0hI1jp;2p;3p;1p;4p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g00DOj20Tg00`Gj2bTg00aKj3ETg008oj1<Tg009Tj1aTg00A0j23Tg00bMj3@Tg00AMj22Tg00COj16Tg00cPj1:Tg00H:j28Tg00dIj39Tg00EnR6j25Tg00Amj2NTg00B^j2PTg00@Oj2MTg00O`j2LTg00Chj2KTg00Dkj2JTg00ERj2?Tg00FIj2HTg00Foj2GTg00:2j1WTg00:Rj1VTg00M<j2ITg00;Pj1UTg00;nj1TTg00<Yj2DTg00N8j2CTg00T@j4BTg00O>j1STg00=<j2RTg00=^j2FTg00>8j2QTg00>dj3>Tg00?>j3`Tg00?]j4_Tg00;2j1^Tg00MZj4]Tg00eHj3\Tg00ebj4ZTg00SBj4OTg00fCj3[Tg00Tkj7YTg00VVj8XTg00X<R0f0R4g00W^R53>p=41?54p=1f1R7=>04p=7P7g00YAR2g00Y`R3P3g00Z@R1P4g00Z`FYp=;f3R8P2P3P3P1f2R2P7P4GXp==P0P7g00[@P4CBp=A1054R91b27p,1MR:?E82P6f4R;g00\NR<#<R=#<#<#aR>,385@:128>#4#6f5R?#:13;>'812;>59:[p,2M'R@?E?;P4f6RA13?>5@:12A>#4#6f8R?#:f7RB/3>RC'812B>RD59:[A@@?CRC%4D#6RDf9RE#:13?>RF'812?>RG59@[%14R@104F'5PBP71NE>RB%1ERH%1>RIf;RJ/2>RK#1[[RLf:RM/P>RN%1MROf<RP/3>RQ#1\I[RR1MJ>RS%4>RT#6RU1L>Q12P>RQ'8,7P[RV1KP>RW105>RXf=RY/2>RZ#110Z>'5[R[1JY>R\10>5R]f>R^/2>R_,0>1?_5'5[R_1H^>R`f?Ra/3>Rb#4\TRc1Ga>Rdf@Re/2>Rf/7e\TRg13e>ReP0fA/2>RhP0P6PO10M7Ri%1JPE%1PRj10Y;R;g00]3Rk#WRl%VkRk1I07Rm%U0Rn%T0RoP01D05Rpg00[g1C0<R<CB,;oRq%S3R3PqC=1Ro1R1P4P2g00]_Rrg00^?Rs'F1Q42=>rsdA`057C_Rsb7b:b;X00%17Rr\@^00P4PaP2O2b6W@W?P7P4O2n2001000000120000000b=b<b5b4b3b2b1b8b913E>R@,07177@12E>#4#6'5PBPLPNPRPSPVPWP[P\P_P`PcPdPgPeP0PhP0P6POPi10J2PEPlPkP01I02P7%^0RiC]PnPo1C0=,A<,;oR=P3P=C=P1Psb7b:b;X00XA010471072[^00^A0P4PAPaP7O3b6X@;X?jP7P4O2n2001000000120000000b=b<b5b4b3b2b1b8b93\P5P8P7P4O2O5WDXI0PCePAPFP?P>1N?>RA%1?12M>#1\I[R?1PE>RC13J>R8#1\I\HRH1MM>RI1L>8/8K,7J\URU1KJ>RJ%1Q10Q>'5\XRQ1JP>RP10>Z1?Z5'5\]R]1HY>RY13^>#4\TRZ1G^>R^12a>/7a\TRTPbP0PfP0PMPEO1REfBRM#:/87=9:4R:PlPkPmPnPo1Ap<,;oP3PqC=P1Psb7b:b;X00Pr\9^00P4fCPMO2b6b>b=b<b5b4b3b2b1b8b9PAP?PCPHPIPUPJPQPPP]PYPZP^PTPbP0PfP0PEP:PlPkPiPn1D0>,Ap,;oP1Psb7b:b;PXP4b6b>b=b<b5b4b3b2b1b8b9CZ10FF17FFRX%4G#6Rs'5PXPs1F0FP4CO3[PGP7P4O1O5XEDCOW>WHP7P4O2n2001000000121000000W1WGWFXB0XC0P7P4O2XB0XC0o"). Qed.

Lemma shadow_blkR_tby u n : 0 < n -> shadow_tby u n -> HAJ.shadow_blkR M u n -> HAJ.shadow_blkR M' u n.
Proof.
ltac2:(KReplay.run1 (kr_t_ShadowRLawsB ()) ["Laws"] "p'0h01Hh14__x1h22H0h32H1h43H10h53H11h63H12h73H13h82H2h92H3h:2H4h;2H5h<2H6h=2H7h>2H8h?2H9h@4__x2hA1qhB2q0hC2q1hD1rhE2r0hF2r1hG3H14hH3H15hI3H16hJ3H17hK3H18hL3H19hM3H20hN6__sat2hO2q2hP2r2hQ7__arithhR3H21hS3H22hT4__ffhU4__p1hV8__varmaphW5__withX6__sat3hY6__sat4hZ4__x3h[4__x4h\6__sat5h]6__sat6h^4__x5h_4__x6h`1jha4__p2hb4__x7hc4__x8hd4__x9he1mhf2P0hg6__sat1hh6__sat7hi2Hjhj4__p3hk1si001shl7__sat10hm7__sat11hn7__sat12ho7__sat13hp6__sat9hq1Ehr3H23hs3H24ht2Hihu2Lohv3Um0hw3Um1hx3Un0hy3Un1hz1ni011nh{1uh|2Dmh}2Dnh~2F0i022Hmi033Hm8i042Hni052M0i062MNi072Rmi082Rni092SBi0:3TBYi0;2Z0i0<1ei0=2n0i0>1zi0?1gi0@1li0A1xp%0p%1p%2p%3p&0p;2p;3p;4p;5p;1p;6p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g00`Gk20RTg00f]j3`Tg00aKj3mTg00gfj4OTg00EnR6j2@Tg00hnR0j2rTg00iHk50BTg00eHj3iTg00ERj2BTg008oj1eTg009Tj1uTg00A0j22Tg00bMj3zTg00AMj21Tg00GUj1ZTg00H:j25Tg00DOj26Tg00cPj1yTg00Amj2ATg00B^j2?Tg00@Oj2<k307Tg00COj1HTg00Chj27k306Tg00Dkj2:Tg00FIj28Tg00Foj2;Tg00:2k10QTg00:Rk10PTg00;2k10OTg00;Pk10NTg00;nk10MTg00<Yj2tTg00=<k20LTg00=^k20KTg00>8k20JTg00>dj3]Tg00?>k30HTg00?]k40GTg00N8k205Tg00O>k10FTg00jPk204Tg00kQk50ETg00ebk40DTg00IVj1ITg00HWk103Tg00I5k202Tg00J^j3lTg00l6k20CTg00l_j3nTg00J5k201Tg00N[j3pTg00O`j2wTg00mHk200Tg00moj2VTg00nKS00j2oTg00nkR4j2vTg00T@j4^Tg00SBj4gTg00fCj3xTg00oEj2}Tg00Rfj6|Tg00oek40ATg00dIk309Tg00Tkj7kTg00UOk60@Tg00M<k20?Tg00VVj8\Tg00MZk40>Tg010?k60ITg00W:k708Tg00KGj3{Tg00L0k20=Tg00L\k30<Tg00V3k30;Tg00W^R5f0R7'6p=f1B57p=0f2R2f1R3/B7'@p=N1B53/@7p>0:g00X<R1?]75#Hp=Ff3R8%y2/53<097p=J1B23/@7p=X1523>0987p=qA]175p=41w23/579]18p==1637,@2p=E16231B75'@p=9A]137p=3f4R91223,w8/575]1p=P1B521637'@p=>P2g00YAR:g00Y`R;P;g00Z@R<P1P3g00XZR=P7C^g00Z`R>Fkp=QP3P:P;P;P<P7J0@p=sP2P:P;P;P<P1P3g00[@P7C^P>Fkp=K20?17p=UP2P:P;P;P<P1P3g00[gP7C^P>Fkp=MP8P:P;P;P<P2P3P7G\p=j15379]12p=GP1P2P3P7H0>p=DP3P:P;P;P<P7J0Ip=b20517p=Wf5R?P:P;P;P<P9P:P;P;P<P8P2K08P3P7G\p=af6R@P:P;P;P<P?P9P8P:P;P;P<P2P3P7G\G\p=C20117p=TA{137p=hA{1379{12p=Lg00_[-0=7p=_g00]3RA@0<37p=SP2P:P;P;P<P3P7K08p=YB0;137p=RP1P3P=P7C^p=dP9P:P;P;P<P8P2P3P:P;P;P<P7P>FkG\p=cP@P:P;P;P<P?P:P;P;P<P9P8P2G\P3P7G\p=[P3P:P;P;P<P7P>Fkp=~%f7S0120R23p,1MR>?`82P4Am>98%07R4?N79P>P?P7P9CO'@Xe1,r1p,2M'R:?`?9P7Am>?9Am:@?AN47@R=P:f7RBP7P@CO'@Xe1,r1P@P?P9P8P7I0B3iY09P7O1AN47?P>P@P7P?CO'@Xe1,r1P0P1P>PBP7P@CO,@=Xe1A`:B@P7f8R=9N47P>f9R0P7P=CO'@P6%03S02?N30P>f:RCP3P0COf;RD=`:CP71B8D-0:8P>f=REP9f<RFCOP6f>RGg00\NS03#eS04#eS05#eS06#uRH,2?5z>11?H#FP>f?RI12@H11@HCJ[Q03#ZS07#ZS08#uRJ,5@S09/2H15GJ/2H,677X7P>f@RKP3Q08#Z#Z#Z#e#e#uS0:CJ[^`1'@A`:IGP712BH9z>K11=H#FP>fBRL120H110HRMCJ[150J/2HfARN/5J/2H,677X7P>fCRO#yRPP3Q0:Cq[^`1'@P6%FMP>PP12CH11CHCq[15CJ/2H15LJ/2H,677X7P>fDRPP3Q0:CJ[^`1A`:OLP711DH#FP>fERM12FH11FHCJ[15EJ/2H15MJ/2H,677X7P>fGRQP3Q0:CJ[^`1fFRR=m:MAN47RP:PQP7PRCO'@Xe1RS,r1P1PSPE%0ES0;?NEMP:PRPEPMCOP01AEHQ0;%0HRS11IH#0[[1?GH%0GS0<12KHRT#0\S[1<IH%4HRU#HRVPKPHPT11KHRTC=[17KH%fHRW11NHRX#0S0=?EXH[1:NH16H5RY11LHRZ=9HZ[18LH12OH#4\U1;OH11PHR[/3P\U12PHR\P111MHR]P115RJ/<H15QJR^PHP^PH11^HDP\V17^HfHR_/5JR`/1HRa?>aH\W1:`HfIRb/5JRc/1HRd=9Hd\Y18cHfJRe/5JRf/2HS0>#4\U1;fHfKRg/5JRh/1HRi/3h\U12hHRjP1fLS0?/5JRk/1HRlP1fURm/5JRn/<HfVRo/5JRpPH12pHS0@11pHS0AC=\V17pHfWRq/5JRr/1HRs?>sH\W1:rHfXS0B/5JRt/1HRu=9Hu\Y18tHfYRv/5JS0C/2HS0D#4\UQ0C/;HfZRw/5JS0E/1HS0FQ0E'3\UQ0E/2HS0GP1f[Rx/5JS0H/1HS0IP1&0QARy&0PAS0J&0O1RA&0N1S0K&0M1Rz1t1HS0L1t15R{5Qz'sS0M20Lz<S0NP7P2g00]_R<g00^?R|+0K20J72=]<|dB0H153H0GS0ObTbVbWg00^_S0P\US0QP7bQS0RbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bgbN:07EHPEPHPEPH11EHDP1AGHQ0<%0T\S[1?IH%0IS0S12NHRT#0\S[1<KHPNPHPTPXC=\V17NHA>ZZH\W1:LH11OHRX=9HX\Y18OH%4\\U1;PH13]M\U12MHR\P111RHRTP11<^HP`PHP`PHPaDP\V17`HA>ddH\W1:cH11fHRa=9Ha\Y18fH%4j\U1;hH13lk\U12kHS0TP1fMS0U/5JRl/1HR^P11<pHPrPH12rHS0VPsC=\V17rHA>uuH\W1:tHQ0C/1HS0WQ0W59H\YQ0C/8HQ0G#4\UQ0E/;HQ0IQ0H'3\UQ0H/2HR|P1f\R</5JS0X/1HR}P1PyQ0JPAQ0KQ0L9Kz{S0YQ0NQ0ObTbVbWPWP7bQS0ZbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bgbN:06GH11GHR~?>~H1AIHQ0SQ0=\S[1?KH%0KS0=12LHR~#0\S[1<NHPLPHP~PZC=\V17LH%0XRZ?EXH\W1:OHA9H[[\Y18PH%4\\U1;MH13TR\U12RHRXP111QHR~P11<`HPcPH12cHS0[PdC=\V17cHA>aaH\W1:fHA9Hii\Y18hHQ0T#4\U1;kH13^l\U12lHS0\P1fNRl/5JS0]/1HP11<rHS0^PtPH12tHS0_PuC=\VS0`17tHS0aQ0WQ0W;>H\WS0bQ0C/:HS0cQ0FQ0F59H\YS0dQ0E/8HS0e%4|\US0fQ0H/;HS0gQ0X,3}\US0hQ0X/2HS0iP1f]R}/5JS0j/1HS0kP1P6Q0<16GHS0lPVPQQ0=16NHS0mQ0RWHWGP3P7O2n2001000000120000000bFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bgbN:07QHPQPH12QHS0RP~C=1A_HS0n%0_S0o11eHR|#0\S[S0p1ANH%0NS0qPZ\S[1?eHS0r%0eS0sQ0?/2HS0t#0\S[S0u1?OH%0O%0\\S[1<PHPMPHP\P]C=\V17MHA>TTH\W1:RHA9H~~\Y18QH12_HS0v#4\U1;_H11bHS0w/3b\U12bHS0xP1P|P1fSR]/<HS0yfTR\PH12\HS0z11\HS0{C=\VS0|17\HS0}11mHRZ#0S0~?EZH\WS101:mHS1111oHS12Q1259H\YS1318oHS1412qHS15#4\US161;qHS17Q0B/1HS18Q0B'3\US19Q0B/2HS1:P111vHS1;P1fRR^/5JS1</<H15]JS1=PHQ1=/2HS1>Q1=/1HS1?C=\VQ1=/7H15\JS1@/1HS1AQ1A;>H\WQ1@/:H11nHS1BQ1B59H\Y18nHQ0@#4\U1;pH13sr\UQ0VP1PuP1faRk/5JS0@/<HS1CfbRh/5JRiPH12iHS1D11iHS1EC=\VS1F17iHS1GfcRf/5JS1H/1HS1IQ1I;>H\WS1JQ1H/:HS1KfdRa/5JS1L/1HS1MQ1M59H\YS1NQ1L/8HS1OfeRc/5JS1P/2HS1Q#4\US1RQ1P/;HS1SffRd/5JS1T/1HS1UQ1T'3\US1VQ1T/2HS1WP1fgS1X/5JS1Y/1HS1ZP1P6%0MS1[16MHS1\PWfQR`%0QS1]16_HS1^Q0ZWMWLP3P7O2n2001000000120000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bgbNbXbY:06_H11_HS1_Q1_;>H1AbH%0bS1`11gHS1a#0\S[1ALH%0LS1b%0[\S[1?gH%0gS1cQ0U/2HS1d#0\S[1?PH%0PS1e%0X\S[1<MHPRPHPXPTC=\V17RHA>~~H\W1:QHQ1_Q1_59H\Y18_HQ0x#4\U1;bH13|e\U12eHS1fP1Q1aP11<\HPmPH12mHS1gPZC=\V17mHQ12#0S1hQ12;EH\W1:oH11qHS1iQ1i59H\Y18qHQ1:#4\UQ0B/;HQ1;/3v\U12vHS1jP111wHS1kP1Q1=/<HS1lQ1@PHQ1@/2HS1mQ1AC=\VS1AQ1@/7HS1nQ1BQ1B;>H\WS1o1:nHS1pQ0AQ0A59H\YS1q18pHS1rQ0V#4\US1s1;rHS1t13ut\US1uQ0_P1Q0WP11<iHQ1HPHQ1H/2HS1vQ1IC=\VQ1H/7HQ1MQ1M;>H\WQ1L/:HQ1P/1HS1wQ1w59H\YQ1P/8HQ1W#4\UQ1T/;HQ1ZQ1Y'3\UQ1Y/2HS1xP1fhS1y/5JS1z/1HS1{P1P6Q0<Q0lfjS1|#0fPRuQ0=Q0mP6Q1`16bHS1}fnS1~#0PoQ1cQ0?/6HS20PyQ0J%U3S21Q0KPzQ03-051R~9Kz{&0F;R;AMz{~S22CjQ0NQ0ObTbVbWX11Q01Q02[^11P7frS01fqRTO2bQWSWRP3P7O2n2001000000120000000WMWLP3P7O2n2001000000120000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bgbNbXbY-04bQ0w#4R[Q0>Q1f'3[%H[Q0>Q1fQ03#uR[3G['@P6%4|R|12gHS0>,3j[S23%H|Q0>=Gj[[S24P:Q0?POPgCOP7Q0?/1HS25#4Q0\Q1d'3[Q0U/1HS1d#4S0\#HQ0]/2HS0]12lHS26;G[[PRPlPH1AlHS27%0l11uHS28#0S29\S[S2:1AQHS2;Q1]Q0w#0\S[S2<1?uHS2=%0u12^HS2>#0\S[S2?1?bHS2@Q1`Q0>#0\S[S2AQ1</?HS2BQ1<#0Q1m#0\S[S2CQ1lQ1AQ1nQ1oQ1pQ1qQ1rQ1sQ1tQ1uQ0_P1Q0WP11<^HS2DP]PH12]HS2E11]HS2FC=\VS2G17]HS2HQ0{#0S2IQ0{;EH\WS2J1:\HS2KA9HZZ\YS2L18mHS2M12oHS2N#4\US2O1;oHRZQ1i/3q\URjQ15P1Q18P11<kHS2PPhPH12hHS2Q11hHS2RC=\VS2S17hHS2T11fHS2UQ2U;>H\WS2V1:fHS2W11aHS2XQ2X59H\YS2Y18aHS2Z12cHS2[#4\US2\1;cHS2]11dHS2^/3d\US2_12dHS2`P1Q1X/1HS2aP1f`R|/5JS2b/<HS2cQ0@PHQ0@/2HS2dQ0@/1HS2eC=\VS2fQ0@/7HS2gQ1EQ1E;>H\WS2h1:iHS2iQ1IQ1I59H\YS2jQ1H/8HS2kQ1L/2HS2l#4\US2mQ1L/;HS2nQ1wQ1P'3\US2oQ1QP1Q1UP1P6%0BS2p16BHS2qPWPo%00S2r16CHS2sP6Q1b16LHS2tPWP<Q1eQ1\Q0ZWSWRP3P7O2S0Zn2001000000120000000WMWLP3P7O2n2001000000120000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]Q27Q2:Q2;Q2<Q2=Q2?Q2@Q2AQ2BQ2CQ1lQ1AQ1nQ1oQ1pQ1qQ1rQ1sQ1tQ1uQ0_P1Q0WP1Q2DQ2GQ2HQ2JQ2KQ2LQ2MQ2OPZPjQ15P1Q18P1Q2PQ2SQ2TQ2VQ2WQ2YQ2ZQ2\Q2]Q2_Q2`P1Q2aP1Q2cQ2fQ2gQ2hQ2iQ2jQ2kQ2mQ2nQ2oQ1QP1Q1UP1P6Q2pQ2qQ1yfpS2O'BPoQ2rQ2sP6Q1bQ2tflS2MftS2L'BP<Q1eQ1\p-0RjPyQ0J%U2S2K?D3AS2JQ0KPzPz1bz9S2HQ04#WRZ9Mz~S2GP;Q2GEaQ0NQ0ObTbVbWX11X@1WUAN2731B32[^11^@1^UjP7Q2O#0fxS2DQ2OQ2MO4bQWSWRP3P7O2n2001000000120000000WMWLP3P7O2n2001000000120000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]I0EQ26,BXPQPHfORX/AHS1u%0XS1t11`HS1s#0\S[S1rQ0nQ0p1?`HS1q%0`S1pQ2E#0\S[S1oQ0rQ0uQ1=/?HS1nQ1=#012nHS1A#0\S[S1lQ1@/<HS2CPnPHQ1AQ1BC=\VS2B17nHS2AQ0AQ0A;>H\WS2@1:pHS2?A9Hss\YS2=18rHS2<Q0_#4\US2;1;tHS2:Q0WQ0C'3\US27Q0DP1Q0FP1Q0yQ0|Q0}Q10Q11Q13Q14Q16Q17Q19Q1:P1Q1;P11<hHS2uPfPH12fHS2vQ2UC=\VS2w17fHS2xQ2XQ2X;>H\WS2y1:aHS2z11cHS2{Q2{59H\YS2|18cHS2}Q2`#4\US2~1;dHS30Q2aQ1X'3\US31Q1X/2HS32P1Q1y/1HS33P1Q1CQ1FQ1GQ1JQ1KQ1NQ1OQ1RQ1SQ1VQ1WP1Q1ZP1P6Q2pQ2qfiRs#0PqQ2rQ2sP6Q1bQ2tfmS34#0S35P}Q1eQ1\PyQ0JQ21Q0KPzPzQ221bz8P;Q22EaQ0NQ0ObTbVbWX11XUjS211@43Q02[^11^UjS02P7fyS36,BTPTQ34O3bQWSWRP3P7O2n2001000000120000000WMWLP3P7O2n2001000000120000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]Q1uQ1rQ0nQ0pQ1qQ1oQ0rQ0uQ1nQ1lQ2CQ2BQ2AQ2@Q2?Q2=Q2<Q2;Q2:Q27Q0DP1Q0FP1Q0yQ0|Q0}Q10Q11Q13Q14Q16Q17Q19Q1:P1Q1;P1Q2uQ2wQ2xQ2yQ2zQ2|Q2}Q2~Q30Q31Q32P1Q33P1Q1CQ1FQ1GQ1JQ1KQ1NQ1OQ1RQ1SQ1VQ1WP1Q1ZP1P6Q2pQ2qPWPqQ2rQ2sP6Q1bQ2tPWP}Q0Zn2001000000120000000WMWLP3P7O2n2001000000120000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]H0DQ0R#0Q0v9z:`S0vQ1_#FS1_P:P^Q0xQ0wCJ[S0RQ0[15`JS0Z/2HS1W,677X7S0[P:P]P3Q0:CJ[^`1S1V'@Q0x9E47PuP31A^HS1S%0^S1RQ2I\S[S2I1AgHS1OQ1cQ1d#0\S[S1d1?\HS1N%0\S1KQ2N#0\S[S1JQ0U/?HS1GQ0U#0S1F12XHS1C#0\S[S311?pHS30%0pQ0_#0\S[S0_Q0^Q0`Q0aQ0bQ0cQ0dQ0eQ0fQ0gQ0hQ0iP1Q0kP11<oHPqPHQ15Q1iC=\V17qHQ18Q18;>H\WQ0B/:HQ1;Q1;59H\Y18vH12wHS0h#4\U1;wH11xHS0g/3x\U12xHS0fP111<HS0eP11<cHPdPHQ2`Q2^C=\V17dHQ2aQ2a;>H\WQ1X/:HQ33Q3359H\YQ1y/8H12sHS0d#4\U1;sHQ1|/1HS0cQ1|'3\UQ1|/2HS0bP1fkS0a/1HS0`P1Q1L/<HS0^Q1PPHQ1QQ1wC=\VS2~Q1P/7HS2}Q1UQ1U;>H\WS2|Q1T/:HS2zQ1ZQ1Z59H\YS2yQ1Y/8HS2xQ1z/2HS2w#4\US2uQ1z/;HS1915sJS17/1HS16Q17'3\US14Q17/2HS13P1Q1|/5JS11/1HS10P1P6Q1R16^I%0]S0}P`Q1K16mLP6%0DS0|16DHS0y%0qS27f^RpQ0;Q0lP6%0R16RH%0xS2:PaQ0oQ1}PyQ0JQ2K9DA2S2;9DA3Q0KPzQ22P;PzQ08#WS089Mz{S2<P;Q22FCQ0NQ0ObTbVbWX11X@1%02S2=Q2=[\4^11^@1S2?P7PPf_S2@PCP@O4bQWsWrP3P7O2n2001000000120000000WSWRP3P7O2n2001000000120000000WMWLP3P7O2n2001000000120000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]Q2>,63Q2>,3311^HS0o#F'@Q1SQ2IQ1OQ1dQ1NQ1JQ1GQ31Q30Q0_1<qHQ0BPHQ1:Q18C=\VQ0B/7HQ1;#0S2AQ1;;EH\W1:vHQ1kQ1k59H\Y18wHQ0f#4\U1;xHQ0e/3<\U12<HS2BP111}HS2CP115pJS1l/<HQ2@/5JS1nPHQ1nPHQ1n/1HS0uDP\VQ1n/7HQ2b/1HS0rQ0r;>H\WQ2b/:HQ2eQ2e59H\YQ0@/8HQ1D#4\U1;iHQ1IQ1H'3\UQ1vP1Q1MP11<}HPpPH12pHS1o11pHS1qC=\V17pHQ2@/1HS0pQ0p;>H\WQ2@/:H11|HS0nQ0n59H\Y18|H12kHS1r#4\U1;kHQ2R/3h\UQ2QP1Q2UP1Q0^Q2~Q2}Q2|Q2zQ2yQ2xQ2uQ19Q14Q13P1Q10P1P6Q1R16^=16]QP`Q1K16mDP6Q1`Q1}16qgPpQ1cQ20P6Q0S16IH16xXPaQ0qQ2tg00_<S0S#I#IS13#I#I#IS14#IS19#IS2u#IS2x#IS2y#IS2z#IS2|#I#TS2}Q03$03-021S03Q2|#TS2|5l1S2~Q2x#TS2xQ2u#TS2u20C1HS0^Q19#TS195n1S1uQ13#TS13Q0^Q0S-011S0S5n1'hS1e'hS373L3L#_Q2}Q2~Q2z#TS2zQ2y#TS2yQ1uQ0^Q14#TS145n1Q1e3L3L3L#_/Sy'SQ0J%U=?D9A%U@S2~7D2%U0?D?A%UB7D87D3S2}Q0KPzPzQ0YP;Q04#Z#WS049Mz{S1u1bzDS385YzP;PzPzQ0MP;Q05#WS39Q0LQ07#e#WS3:5p1S3;Q04'R5QzP;PzPzQ0YP;1bzFS3<Q05#Z#WS05Q0L5Kz5YzP;PzPzQ0MP;Q07#WS071t1J'RQ0LQ06#WS3=5p1Q05'R5QzP;PzPzQ0YP;1bzES3>Q08Q0L5Kz5YzP;PzPzQ0MP;Q07Q0L=p1ZQ08'R5QzP;PzQ3:9Kz~P;PzPzQ08=Qz{S08P;PzQ3=/dZDcP;PzQ2<P;PzQ399Mz{Q39Q075Mz5YzP;PzQ079Kz{P;AKz~ZS3?CjFCFCF[F[F[F[F[F[Q0NQ0ObTbVbWX11X@1XZ1X[1X^1X_1Xb1Xc1Xd1XUjXajXjj20:?C\WQ0Q1wHBS3@=G?@[Q0y,@E\WQ0QQ09PHPDPFC=[Q0y,@K\WQ0QQ3@=G=F[16@D%4E13I0[Q0<%0FS09?NFD%fF16DF[[[[[[[[[[[^11^@1^Z1^[1^^1^_1^b1^c1^d1^Uj^aj^jjP7Q1RQ1c16PHPgQ0?P^PMPPQ2Dp+01AP]Q2@PbPePuP`PqQ0BP0PfP@Q2Lp+01@S0BOGbQWsWrP3P7O2n2001000000121000000WSWRP3P7O2n2001000000121000000WMWLP3P7O2n2001000000121000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]3iP5PLP3P7O2O5WiX`1Q0veQ0RQ1VQ1_PXQ0x1A`HQ1pQ2F#0S1V\S[1AeHQ0sQ25#0\S[1?]HQ0}Q1g#0\S[Q0?/?HQ0?#0Q26#0\S[1?nH%0nQ0V#0\S[1<lHPXPHQ1C11XHS0VC=\V17XHQ29Q28;EH\W1:uHQ1sQ1s59H\Y18`HQ2>#4\U1;^HQ2F/3]\UQ2EP1Q0{P1Q0j/<HQ1lPHQ1lPHQ1l/1HS29DP\VQ1l/7HQ0uQ0u;>H\WQ1n/:HQ0rQ0r59H\YQ2b/8HQ2d#4\UQ0@/;HQ1E/3i\UQ1DP1Q1IP11<aHS1IPcPHQ2[Q2{C=\VS1D17cHS0uQ2^Q2^;>H\WS0?1:dHS0sQ2aQ2a59H\YS25Q1X/8HS1pQ1y/2H#4\US0RQ1y/;HS0v11sHS0q/3s\US2tQ0dP1Q0cP1Q1H/<HS1RQ1LPHQ2lQ1MC=\VS3AQ1L/7HS3BQ1wQ1w;>H\WS3CQ1P/:HS1PQ1UQ1U59H\YS3DQ1T/8HS3EQ1x#4\US3FQ1Y/;HS3GQ1{Q1z'3\US3HQ2wP1Q16P1P6Q2pQ2qQ1]PvQ2rQ2sP6Q1`Q1}Q1cQ2@Q1cQ20PdPvO1P>f{S2pPlQ0UCJPyQ0JQ2;?D3AQ0KPzQ22P;PzQ3:9Mz{S2;P;Q22FCQ0NQ0ObTbVbWX11X@1Q2?P7PNPuP<PBO4bQbfWSWRP3P7O2n2001000000120000000WMWLP3P7O2n2001000000120000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bpblbmbnboQ0x12`HRM+00Q0x/6MQ0x/VM'oQ00Q1fQ2>'6Q1fQ2>'VQ0>Q2E'6S1fQ0>Q2E'3Q2F#F'@'vP7Q1fQ0tQ0z'6S0xQ0tQ0z'3S0zQ0{#FS2s'@S2?;i7WuP7O1Q0>Q2E'VQ0xQ2?Q0zQ2s1A\HS2sQ1KQ1h\S[S1KQ0U/AHS1hQ1FQ0V#0\S[S1F1?oHS0z%0oQ1:#0\S[S1:1?XHS2EQ1t%0M\S[S1t1?tHS0>%0tQ0G#0\S[S1f1<`HP^PHQ2>Q0oC=\V17^HQ1VQ2F;EH\W1:]HQ0{Q0{59H\Y18\HQ1g#4\U1;mHQ12/3o\UQ2NP1Q1iP11<|HPkPHQ1r11kHRoC=\V17kHQ2RQ2R;>H\W1:hHQ2UQ2U59H\Y18fH12aHS1r#4\U1;aHQ2{/3c\UQ2[P1Q2^P1Q1Y/<HS2^Q1zPHQ2wQ1{C=\VS2[Q1z/7HS2NQ16Q16;>H\WS12Q17/:HS1gQ10Q1059H\YS10Q11/8HS0{Q0a/5JR\/2HS1V#4\US2F1;\HS0oQ2M/5JR^/1HRM/3^\US2>12^HS3IP1Q34/5J/1HS3JP1Q1T/<HS1TQ1YPHQ1xQ1ZC=\VS1ZQ1Y/7HS1YQ1{Q1{;>H\WS1{Q1z/:HS1zQ16Q1659H\YS1xQ17/8HS17Q11/2H#4\US3KQ11/;HS1111\H/3\\US3LQ1VP1PMP1P6Q0<Q0l13QKP<Q0=Q0mP6Q1`Q1}13gPPhQ1cQ20PsP<O1S1}P>f~S1`#yS0<PlQ0UCqPyQ0J%U9S0U9DA2%U8S3M?D9A7D3Q0KPzP1P~g010cS3NPZC^,~zS3OP;PzQ04=Qz{S3P,szS3QP;PzQ2GP;PzQ2;P;PzQ1uP;Pz1d~ZDcS2;FCFCQ0NQ0ObTbVbWX11X@1XZ1X[11V73S2G%48Q0P[1B28%0@R\13?@\\[S3R[[[^11^@1^Z1^[1P7P_PXPbPuPxPpP|PBP8O9bQbfWSWRP3P7O2n2001000000121000000WMWLP3P7O2n2001000000121000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bpblbmbnboQ2sQ1KQ1hQ1FQ0zQ1:Q2EQ1tQ0>Q1f1<vHPwPHQ0hQ1kC=\V17wHQ0gQ0g;>H\W1:xHQ0eQ0e59H\Y18<H12}HR^#4\U1;}HQ1q/3p\UQ1oP1Q0pP1Q2cQ2fQ2gQ2hQ2iQ2jQ2kQ2mQ2nQ2oQ1QP1Q1UP1Q2@/<HP|PHP|PHQ0nDP\V17|HA>ooH\W1:kHQ2RQ2R59H\Y18hHQ2v#4\U1;fHQ2X/3a\UQ1rP1Q2{P1Q1TQ1ZQ1YQ1{Q1zQ1xQ17Q3KQ11Q3LQ1VP1PMP1P6Q1[Q1\%FRP<Q1]Q1^P6Q0|Q0y%FePhQ0;Q0lQ1}P>Q0<PKPICqQ03Q2y5l1Q2xQ0^Q2u5n1S0^Q19Q13Q0S'h3L3L#_/SyQ0JQ0UQ2~7D2%U??D8A7D3Q0KPzPzQ0MP;PzQ07Q0LQ395p1Q04'R'dDcS2~P;PzPzQ0MP;PzQ3;/R~,dZDcP;PzP1Q39Q3NQ3:C^,~zP;PzQ3QP;PzQ22P;PzQ1uP;PzPzQ079Mz{S3NQ07=MzZP;PzAKz{ZS07P;AQz~{,szCjEaFCFCFCQ0NQ0ObTbVbWX11X@1XZ1X[1X^1X_1Q0QP8PHP9P?C=[S3;Q0QQ3@=G82[1V?B%4BQ0P[%09S3@Q2r%0=S0M?N=B%f=%4=Q0P[[[[[[[[[^11^@1^Z1^[1^^1^_1P7PuPNPLfwR{Q0BPXPQPmPxPpPBP8fsRAQ1`O>bQbfWSWRP3P7O2n2001000000121000000WMWLP3P7O2n2001000000121000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bpblbmbnboCg3xWtP7O1n200110000021010@1110?bkQ0wPEP7O1S0wO5Y03Q0[Q1SQ2IQ1OQ1dQ1NQ1JQ1GQ31Q30Q0_15XJRI/?H%0IQ1W#0\S[15uJ/<HQ0ZPHQ1WQ0Z/1HC=\VQ0Z/7HQ1</1HRR?>RH\WQ1</:HQ1?Q1?59H\YQ1=/8HQ1m#4\UQ1@/;HQ1B/3n\UQ1AP1Q0AP1Q1n/<HQ2bPHQ2b/2HS0AQ0rC=\VQ2b/7HQ2eQ2e;>H\WQ0@/:HQ1EQ1E59H\Y18iHQ1v#4\UQ1H/;HQ1MQ1L'3\UQ2lP1Q1wP11<pHQ2@PHQ2@/2HS1wQ0pC=\VQ2@/7HQ0n#0S0pQ0n;EH\W1:|HA9Hoo\Y18kHQ2Q#4\U1;hHQ2U/3f\UQ2vP1Q2XP1Q34/<HQ1~PHQ1~PHQ1~/1HDP\VQ1~/7HfoRh/1HS2XQ2X;>H\W1:hHQ2O/1HRo=9Ho\YQ2O/8H12TH#4\U1;THQ01/1HS2vQ01'3\UQ01/2HS2UP111AHRnP1P6P4167HS0nQ35PxQ2=168HRRP6Q0|Q0y%0TPkQ0;Q0lQ21Q02P7fuRMf}'BPMPTO3bQWSWRP3P7O2n2001000000120000000WMWLP3P7O2n2001000000120000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]bh-04eQ23Q24'@P6Q1a#4S1aQ0TQ0t'3[Q1a#HQ0TQ0t;G[[P:PmP8Q0:CJP7Q0\Q0]Q26'3[11lH#F12IHQ1C;G[[PmP@Q0V/}5Q0V#4RI%HI'oQ00Q28#4RI%HIQ0MP7Q1s#4S1s1AwHS0M%0wQ0e#0\S[S0e1A]HS28Q0}Q0~\S[S0}1?<HS0~%0<S0VQ1o#0\S[S1C1?mHS0\%0mQ15#0\S[S15Q1l/?HS26Q1l#0Q0A#0\S[S0A1?rHS1l%0rQ0D#0\S[S0]1<tHS0tQ0CPHQ0DQ0WC=\VS0WQ0C/7HS0CQ0FQ0F;>H\WS0FQ0E/:HS0EQ0IQ0I59H\YS0IQ0H/8HS0DQ0i#4\US0iQ0X/;HS0XQ0kQ0j'3\US0kQ0j/2HRtP1Q29P1Q2^Q2[Q2NQ12Q1gQ10Q0{Q2FQ0oQ2>Q3IP1Q3JP11<dHS0jQ1XPHQ32Q2aC=\VS32Q1X/7HS0TQ33Q33;>H\WS33Q1y/:HS1aQ0qQ0q59H\YS0q18sHS24Q0b#4\US0bQ1|/;HS23Q0`Q0a'3\US0`Q0a/2HS0aP1Q2M/1HS2MP11<MHS02fvRrPH12rHS2111rHS35C=\VS1M17rHS1L11{HS1HQ1H;>H\WS1v1:{HS1EQ2D/1HRm=9Hm\YS0@Q2D/8HS2eQ36/2H#4\US2bQ36/;HS36fzRm/1H/3m\US0r12mHS1AP1Q2p/1HS1BP1P6P4Q0nQ0VPfQ2=P6Q0|Q0y%0|R]PsQ0;Q0lPpPwO113lKQ2yQ2xQ06$03-021S06Q2u5l1Q37'h3L#_RI1SIy,SI'SQ0JQ2}Q0KPzQ2~P;PzQ3PP;PzQ05Q395QzP;PzQ05=Mz~S3PQ385YzP;PzPzQ08,szS2yP;PzQ3=Q3:1t1[RI'R'dDcS37P;PzPzQ08P;PzQ3=Q3:'dDcS3=P;PzQ2<P;PzQ3NQ3<5YzP;PzQ07P;Q22CjS22FCFCFCFCQ0NQ0ObTbVbWX11X@1XZ1X[1X^1X_1Xb1Xc1Xd1XUjXajQ3;%4?13C?AXD8F%4CQ0P[AGFC[[%4DS0713ED[Q09Q2r/@N%f0Q2r[[[[[[[[[^11^@1^Z1^[1^^1^_1^b1^c1^d1^Uj^ajP7Q1`p+01GR:'B16cbPuPbPCPDPNPLQ1`P:PcPQP<P3PaQ1yPsPBPmp+01FODbQbvWSWRP3P7O2n2001000000121000000XMRWLP3P7O2n2001000000121000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]bhY0<P7O1Q1s#HQ0MQ0eQ28Q0}Q0~Q1CQ0\Q15Q26Q0AQ1lQ0]Q0tQ0WQ0CQ0FQ0EQ0IQ0DQ0iQ0XQ0kPtP1Q29P1Q2^Q2[Q2NQ12Q1gQ10Q0{Q2FQ0oQ2>Q3IP1Q3JP1Q0jQ32Q0TQ33Q1aQ0qQ24Q0bQ23Q0`Q0aP1Q2MP1Q02Q1MQ1LQ1vQ1EQ0@Q2eQ2bQ36Q0rQ1AP1Q1BP1P6P4Q0nQ0VPfQ2=P6Q0|Q0yP]PsQ0;Q0lP}PwO1AGlK[PTPxO1P>P:PNPKCJQ03Q195l1Q14'h#_Q2|Q2zQ06Q2x5l1Q0^Q1e3L3L#_RN1SNy'S'SQ0JQ2}Q0KPzPzQ0YP;Q38Q04Q0L5Kz5YzP;PzQ2~P;PzQ3QP;PzQ05Q39/RI5QzP;PzQ3PQ3<5YzP;PzQ37P;PzQ3=P;PzQ2<P;PzQ1uP;PzPzQ3NQ3>P;Q22EaFCFCFCFCF[Q0NQ0ObTbVbWX11X@1XZ1X[1X^1X_1Xb1Xc1Xd1XUjXajXjjAEC?H\WQ0QP9PHP?P@C=[%4@Q0P[AGD@[AXF9GQ07Q0P[AGED[[%4F13GF[Q0;Q09Q0|/@P%fDQ0|[[[[[[[[[[[^11^@1^Z1^[1^^1^_1^b1^c1^d1^Uj^aj^jjP7Q0Bp+01HRP'B16deQ1bP`PePDPFPLPOQ0BPPPdPQP_P}P2PcPsQ1|P=P9Q2pP:OGbQbfbwWSWRP3P7O2n2001000000121000000XMRWLP3P7O2n2001000000121000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]bhY0=P7O1n200110000021110<11101bkQ1i/}5Q1i#4R5%H5'oQ00Q18#4R5%H5Q1j,6=Q1j,3=Q1;#4R5#HRR'@'vP7Q0h,60R:Q0h,30Q1k#F'@P1Q0GQ1>16C77XCZ0>1RcP=Q0hQ0wE|Q1</2H/B0R_/@:1AxHQ2:Q2C#0\S[Q2sQ1K1?}H%0}Q1w#0\S[Q0zQ1:Q1n/?HQ1n#0Q2d#0\S[Q0>Q1fQ2PQ2SQ2TQ2VQ2WQ2YQ2ZQ2\Q2]Q2_Q2`P1Q2aP1Q2cQ2fQ2gQ2hQ2iQ2jQ2kQ2mQ2nQ2oQ1QP1Q1UP115hJ/<HQ2O/5JR:PHP:PH11:HDP\V17:H15TJR:/1HRP?>PH\W1::HQ01/5JR:/1HRP=9HP\Y18:H15AJRP/2HRO#4\U1;PHQ2L/5JRe/1HR`/3e\U12eHP115MJRG/1HRNP1Q1~/<HPhPHPhPHQ2XDP\V17hHA>ooH\WQ2O/:H11THRo=9Ho\Y18THQ2U#4\UQ01/;H13nA\U12AHP1Q2L/1HRoP1P6Q1[Q1\16}QPaQ1]Q1^P6Q3@169HR}16kgQ1|Q2qQ1yPxO113KlPyQ0JQ2JQ0KPzPzQ2HQ3?P;Q3?EaQ0NQ0ObTbVbWX11X@1XUjAE2731632[^11^@1^UjP71BbdPuPdP<O4bQbxWSXR\P3P7O2n2001000000120000000WMWLP3P7O2n2001000000120000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]bhbi3iXq5P7O1P1Q0GPcP=Q0h/5[R=PFP7O1E|AE_0=Q0f-00CQ0f,6CQ0f,VC'oQ00Q2B,6DQ2B,VD16F^RD13F^Q2C#F'@'vP7Q1o,6ER=Q1o,3EREQ1q#FR_'@R0;i7XuDP7O11VF^PEP_1ApH%0pQ0p\S[1AqHQ27Q2A\S[1?|HQ2Q#0\S\]1?vH%0vQ0f#0\S[1?iH%0iQ2l#0\S[Q0H/?HQ0H#0%0t\S[Q1IQ1DQ0uQ0?Q0sQ25Q1pQ0RQ0vQ2tQ0dP1Q0cP1Q1RQ3AQ3BQ3CQ1PQ3DQ3EQ3FQ3GQ3HQ2wP1Q16P11<:HPPPHPO11PHC=\V17PHA>``H\W1:eHA9HNN\Y18GH15rJRG/2H#4\U1;GH15{JR{/1H/3{\U12{HP1Q2D/5J/1HP11<THQ01PHQ2UQ2vC=\VQ01/7HA>nnH\W1:AHA9Hoo\YQ2L/8H12MH#4\U1;MHQ35/3r\UQ21P1Q1HP1P6Q1[Q1\13|QQ1XQ1]Q1^P6Q3@P}13agQ34Q2qQ1|PpO1AGKl[PyQ0JQ2KQ3MQ0U7D97D3Q0KPzQ3OP;PzQ2yP;PzPz1bz@1RZI9Kz~P;PzQ2<P;Q2;CjEaFCQ0NQ0ObTbVbWX11X@1XZ1X[1XUjQ2G%49Q0P[158[9E@2Q3R[[[^11^@1^Z1^[1^UjP71BbsPXPCPuPsP<P|Q2@PBP8O:bQbyWSXR\P3P7O2n2001000000121000000WMWLP3P7O2n2001000000121000000bPbObKbJbIbHbGbFbCb7b6b5b4b?bEbBb>b=b<b;b:bDbAb9b8b3b2b0bNbXbYb\b]bhP9Cg9x=0WtP7O1n200110000021010@1110?bkbiXqRP7O1n200110000021110<11101bkQ0:PLP@P?O2O5WwWvP3P7O2n2001000000121000000b0WiX`1CgCgc05c06WyWxP3P7O2n2001000000121000000b0c08b}c07b|CgH0A3xW~WfP3P7O2n2001000000121000000W0Y0;P3P7O2n2001000000121000000W0Y02P3P7O2n2001000000121000000W0Xe1P3P7O2n200100000012110A000W0P7O1n200100000021000011000W0Y0:Y04Xz1X{1P3P7O2Xz1X{1o"). Qed.

(* [comment removed for export] *)
Lemma shadow_tby_in u n j : 0 <= u -> u mod 8 = 0 -> 0 < n -> 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) ->
  in_shadow_of u n (HeapIfaceA.S u + j).
Proof.
ltac2:(KReplay.run1 (kr_t_ShadowRLawsB ()) ["Laws"] "h01Hh12H0h22H1h32H2h42H3h52H4h62H5h72H6h82H7h92H9h:7__sat10h;7__sat11h<6__sat9h=1qh>2q0h?1rh@2r0hA7__sat12hB7__arithhC4__ffhD8__varmaphE5__withF4__x1hG4__x2hH4__x3hI4__x4hJ4__x5hK2DUhL3H10hM3H11hN4__p1hO4__x6hP1jhQ1nhR1uhS1zhT2DNhU3H12hV3H13hW3H14hX3H15hY3H16hZ2H8h[2HIh\2Hjh]3Hj0h^2Hnh_2Huh`2RNha7__sat13hb2q1hc2r1p%0p&0p;1p;2p;3p;4p;6p;7p;5p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj1RTg009Tj1`Tg00AMj20Tg00DOj28Tg00A0j22Tg00COj1\Tg00EnR6j2DTg00nkj2^Tg00Amj3Nj2LTg00B^j2Kj3STg00@Oj2?j3]Tg00Chj2<k305Tg00Dkj2=Tg00FIj2;Tg00Foj2:Tg00:2j1tTg00:Rj1qTg00;2j1pTg00;Pj1nTg00;nj1mTg00<Yj2TTg00=<j2kTg00=^j2jTg00>8j2iTg00>dj3MTg00?>j3hTg00?]j4gTg00O`j2PTg00Rfj6eTg00H:j25Tg011Jk106Tg00ERj29Tg00HWk104Tg00I5k203Tg00IVj1JTg00J5j2ITg00J^j3QTg00l6k202Tg00l_j3cTg00L0j2bTg00L\j3aTg00M<j2XTg00O>j1yTg00GUj1WTg010?j6xTg00N[j3VTg00N8j2dTg011kj7sTg00Q[j3rTg012Oj5vTg00cPj1wTg013;j3oTg00T@j4ZTg00Tkj7zTg00UOj6{Tg00Q>j2|Tg00KGj3}Tg00MZj4~Tg00W:k700Tg00VVk801Tg00V3j3lTg00W^R0f0R4'9p=1g00X<R5?M40p=4f1R7=M54p=3f3R2f2R3/P7/545M5p=61874,D3p=Y18371940'Dp=>19031874'Dp=BP5P7g00XZP4CZp=OP7g00YAR1g00Y`R8P8g00Z@R9P4g00Z`Fzp=7P7P1P8P8P9P4E{p=_15749M53p=fP5P7g00[@P4CZp=[1537/|4p=AA}574p=CP5P3P7P4C~p=E1d54p=GP5P7g00[gP4CZp=FP3P1P8P8P9P7P4K00p=UP2P1P8P8P9P3P7P4L01p=@Al574p=H1907/D4p=u%13R:g00\NR;#RS00#RR<#R#`R=,02#41802%12f4R>f5R?/2=R@'813>@10?=#4#\'D'^f7R@AN@=>%1=RAf8RB/0=RC#1[1L@=%1@RDf9RE/0=RF#1\A[1KB=%1Bf:RG/2=RH#1\A[1?E=%4=RI#\RJPGP=PH10G=RHC6[1<G=180=RKf;RL/0=RM#1RN?YM=[1=L=18=0RMf<RO/0=RP=>=P[1;O=f=RQ/2=RR#4\I1:Q=f>RS/0=RT/3S\I12S=RUP5f?RV/0=RWP5fARX/?=fBRYP=12Y=RZ10Y=R[C6\J1<Y=fCR\/0=R]?B]=\K1=\=fDR^/0=R_=>=_\M1;^=fER`/2=S01#4\I1:`=fFRa/0=Rb/3a\I12a=RcP5fGRd/0=ReP5g00]3Rf#tRg%qfRh%p5Ri%n5Rj%m5Rk1T5=Rl1T50Rm'O,7k'_S021kk9RnP4P3g00]_Rog00^?Rp'j1i43=MopdAh507CgRpbCbDbEg00^_S03\IS04P4bBRob@b>b9b8b7b6b5b?b=b4b3b2b1b0b<b:b;7]=P@P=12@=10@=C6P5PC12E=,P=RC=fE4XS5P4P0P>EePBP=12B=P0C6P515C013G4XS5P4PC&06CEe13ECANG=@PN\AASL=B12O=RN#1\A1LL=%1L10Q=#1\ARq[1KO=%1ORr%1U\ARs[1?Q=PSP=PUPTC6\J1<S=%1WRU?YW=\K1=V=f@Rt/0=Ru=>=u\M1;t=12X=Rv#4\I1:X=13[Y\IPZP5P]P51?`=PaP=PcPbC6\J1<a=ABee=\K1=d=fHRw/0=Rx=>=x\M1;w=fIRy/2=#4\I1:y=fJRz/0=R{/3z\I12z=R|P5fKR}/0=R~P5Pob@b>b9b8b7b6b5b?b=b4b3b2b1b0b<b:b;bA9]E=AfECFANL=B%1P\AASO=E%1R\A1LO=%1T\AS05\r1KQ=%1QRr12V=RT#1\AS06[1?S=PVP=PTPWC6\J1<V=%1uS07?Yu=\K1=t=10X=RW=>=W\M1;X=%4Z\I1:Y=13]\\I12\=RZP5P_P51?a=S08PdP=12d=S09PeC6\JS0:1<d=S0;ABxx=\KS0<1=w=S0=10y=RT=>=T\MS0>1;y=S0?%4|\IS0@1:z=S0A13~}\IS0B12}=R~P5fLR|/0=RRP5PgPhPiPj1[ml,7kS0CPnPpbCbDbEPKP4bBS0Db@b>b9b8b7b6b5b?b=b4b3b2b1b0b<b:b;bA:05G=ABHH=%`;RH9AOLRPP=15NGRNANO=ES0EPqASQ=GS0FPs1LQ=ROPU\A\rRr1KS=RU%1SRC12t=RF#1\A[Ro1?V=PtP=PFPuC6\J1<t=ABWW=\K1=X=A>=[[\M1;Y=%4Z\I1:\=13_^\I12^=RuP510`=RFP51?d=PwP=12w=PxC6\J1<w=ABTT=\K1=y=A>={{\M1;z=%4~\I1:}=13R|\I12|=P5fMR{/0=P5P6PD18@=PKPY%1E18G=Q0DWMWLP7P4O2n2001000000120000000b@b>b9b8b7b6b5b?b=b4b3b2b1b0b<b:b;bAQ0EPqQ0FPsPOPrPUPo1?t=PXP=PvPWC6\J1<X=AB[[=\K1=Y=A>=]]\M1;\=%4u\I1:^=13F`\IQ01P5PbP5Q08Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BP~P5PRP5P6%14S0B184=S0A15E{,P=fORRfNR~;AHRb'9PY182=Rup-0R[&04;-035RWg00_<Ro#J#JRU#JRr#JRO#JRs#J,I55Q51I5ORO9Q5W2025=Rq1I5rRr5c51I5URU1I5oRo'C'C'C'Cg00_[RT'b1I5s9Q5WAQ5WrAc5qU/Co'C'C,CO/bT=afg5afPh1X5>Rf1X5?RT7E3f6RO,X59Ei27E7PjPkPkQ0C%y8Ro%W;RU#W#GRq,Fm,7kRrPkP1P8P8P9PBEx5UkC@PoPkPkQ02Po%G<RW%RU#GRs9V5l/Hq'O,7kC@PoPkPrPoPk%GURU1d5;R;9V5l'O,7kPoPkPkP1P8P8P9Q00#GR9/[s,7k1O9s,7k1Oqm,7k,_k5UkFsPoPk1[mW,7kPo1H;9Rq9V5l1HUW1T5H5r5'F,7kC@C@C@C@C@C@PnPpbCbDbEXF5XG5XH5XI5XJ5XO5WN1uO@\KQ04P?P=POP@C6[1P=2,3?18?B13?B%4EQ03['D'^180B15O@,P=AABEH'9[[[\D[[^F5^G5^H5^I5^J5^O5^N[P418?=P?POfRR[fSRDfQRBPQPGPLP3PyP|P~O=bBWMXL:P7P4O2n2001000000121000000b@b>b9b8b7b6b5b?b=b4b3b2b1b0b<b:b;bADv12P=,9NANQ=GQ05ASS=LQ061LS=Q07\A\C1KV=%1V%1v\A[AAXtHRX/K=%1XAA\YH/2=#1\A[1?Y=P\P=PZP]C6\J1<\=AB__=\K1=^=A>=FF\M1;`=%4c\I1:a=13ed\IQ09P5PxP5AAywH/?=AAzyHRyP=12y=10y=C6\J1<y=AA}zHRz/0=Ry?By=\K1=z=AA|}HRz/0=Ry=>=y\M1;z=AA{|HR|/2=#4\I1:|=AA~{HR~/0=/3~\I12~=P510b=P51?R=fPRbP=12b=10b=C6\J1<b=10B=Rb?Bb=\K1=B=10[=RB=>=B\M1;[=12D=#4\I1:D=fTRD/0=/3D\I12D=P5fU/0=P5P6Q0BQ0Ag014?R6,5tRtfVR=,5tRt'915E6,9t'DP}PgPhAEf3iAET?i?E2i7E7PjPk1H;U/FW,7kPoPk%W<#G,Fm,7kPoPk1FmU,7kPo1HqURU,Fq,7k1HW9,FU,7k5UkC@C@C@PnPpbCbDbEXF5XG5XH5XI5XJ51543/92%1?%1>152>R2152?R2'915O>,92'D[[[^F5^G5^H5^I5^J5P4P?PQfZP6P^PRP3P=O8bBXYuXX:P7P4O2n2001000000121000000bcbbbWbVbUbMbLb@b>b9b8b7b6b5b?b=b4b3b2b1b0b<b:b;bAbab[b`bTbKbKbK%w@/5?9o@OeW\W]W^WZW_XP5XQ5XR5P3P7P4O3XP5XQ5XR5o"). Qed.

Lemma shadow_blkR_frame u n : 0 <= u -> u mod 8 = 0 -> 0 < n ->
  (forall a, in_shadow_of u n a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> HAJ.shadow_blkR M u n -> HAJ.shadow_blkR M' u n.
Proof.
ltac2:(KReplay.run1 (kr_t_ShadowRLawsB ()) ["Laws"] "h01nh11uh22AGh32Bth42H8h52Hjh63Hj0h72Hnh82Huh91ah:1jh;1oh<1vp;2p;1p;3p;8p;6p;4p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g00ERj29Tg008oj10Tg009Tj1?Tg00AMj23Tg00>dj31Tg00DOj26Tg013;j3CTg0159j14Tg015Wj1=Tg016:j1<Tg016\j22Tg00A0j2;Tg00COj1:Tg00Enj2FTg00nkj2ETg00cPj18Tg00H:j27Tg00dIj35Tg017Bj2DTg017dj8BTg00P`j6@Tg00`Gj2ATg018kj4>Tg00X<R6g00W^R0f1R4'9f2R5g00\N#0#0#0R7#?R2'3=1601605f5R3f4R1f0R83C%47R9#=R:#<R;p,2M'R<%07#0#0#4R7/24R=O1p,1MR>P=O131[^96P3P1P41908f6R=/;2R?,64A164?13=2=160#:'F'Ef9R0#8f3R2'7=5>8P;P>f:R>#8/71R?,27R7O11295,D:91;8X;;P8P<P7O1P3P?P>P0P1f8f7P=P2P5GBO2E@A5<?4eW3X<6W5W6X:61A31eC>W2W7W4W8X06X16P4P8O2X06W1o"). Qed.

Lemma shadow_blk_frame u n : 0 <= u -> u mod 8 = 0 -> 0 < n ->
  (forall a, in_shadow_of u n a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> shadow_blk M u n -> shadow_blk M' u n.
Proof.
ltac2:(KReplay.run1 (kr_t_ShadowRLawsB ()) ["Laws"] "h01nh11uh22AGh32Bth42H8h52Hjh63Hj0h72Hnh82Huh91ah:1jh;1oh<1vp;2p;1p;3p;8p;6p;4p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp605000R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g00ERj29Tg008oj10Tg009Tj1?Tg00AMj23Tg00>dj31Tg00DOj26Tg013;j3CTg0159j14Tg015Wj1=Tg016:j1<Tg016\j22Tg00A0j2;Tg00COj1:Tg00Enj2FTg00nkj2ETg00cPj18Tg00H:j27Tg00dIj35Tg017Bj2DTg017dj8BTg00P`j6@Tg00`Gj2ATg00iHj4>Tg00X<R6g00W^R0f1R4'9f2R5g00\N#0#0#0R7#?R2'3=1601605f5R3f4R1f0R83C%47R9#=R:#<R;p,2M'R<%07#0#0#4R7/24R=O1p,1MR>P=O131[^96P3P1P41908f6R=/;2R?,64A164?13=2=160#:'F'Ef9R0#8f3R2'7=5>8P;P>f:R>#8/71R?,27R7O11295,D:91;8X;;P8P<P7O1P3P?P>P0P1f8f7P=P2P5GBO2E@A5<?4eW3X<6W5W6X:61A31eC>W2W7W4W8X06X16P4P8O2X06W1o"). Qed.
End Laws.

(* [comment removed for export] *)
Lemma shadow_blkR_bytes (M : word -> option byte) u n : 0 < n -> HAJ.shadow_blkR M u n ->
  forall i, 0 <= i -> (i < n / 8 \/ (i = n / 8 /\ n mod 8 <> 0)) -> exists v, byte_at M (HeapIfaceA.S u + i) v.
Proof.
ltac2:(KReplay.run1 (kr_t_ShadowRLawsB ()) [] "p'0h01Hh14__x1h21vh32H0h42H1h52H2h62H3h76__sat2h84__x2h91qh:1rh;3H10h<3H11h=3H12h>3H13h?3H14h@3H15hA3H16hB3H17hC3H18hD2H4hE2H5hF2H6hG2H7hH2H8hI2H9hJ6__sat3hK6__sat4hL2q0hM2q1hN2q2hO2r0hP2r1hQ2r2hR3H19hS3H20hT7__arithhU4__ffhV8__varmaphW5__withX3H21hY3H22hZ4__p1h[6__sat5h\6__sat6h]4__x3h^6__sat7h_1ih`6__sat1ha1si001shb1Ehc2Enhd3Um0he4__x4hf1jhg1mhh1zhi2Hihj2P0hk3Un0hl3Un1hm2Eihn3Hi0ho1Mhp3Um1hq2Z0hr4__x5hs1ni011nht1uhu2Dmhv2Dnhw2F0hx3Hi'hy2Hmhz3Hm'h{2Hnh|2Loh}2MNh~2Nii022Rmi032Rni041ei051gi061li071xp%0p%1p%2p&0p;1p;2p;3p;4p;5p;7p;8p;6p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9P0p1002Pp4p710R1p8P0p1002gR2p4p710R3p8P0P2p4p7210p8P0p1003Cp4p710R2p8P0p1003dR4p4p710p8P0P4p4p7210p8P0p1004AR4p4p710R5p8P0P4p4p7210R4p8P0p1004Up4p710R6p8P0p10051p4p710R0p8p1005Jp4p70R7P1p8P7P3p8P7P2p8P7p1006Hp4p710p8P7p1006mp4p710p8P7p1007Mp4p710p8P7p1007jR2p4p710p8P7P2p4p7210p8P7p1008>p4p710p8P7P0p8p1008Zp4p710R0P5p8P0P4p8P0P6p8g008oj1OTg0159j1sTg015Wj1lTg016:j1wTg00DOj26Tg00f]k309Tg00aKj3pTg00ERj2?Tg00EnR6j2ATg00gfj4UTg009Tj1aTg00A0j21Tg00AMj20Tg00bMj3dTg00cPj1QTg00Amj2BTg00B^j2@Tg00@Oj29j3oTg00COj1CTg00Chj2:j3nTg00Dkj2=Tg00FIj2;Tg00Foj28Tg00:2j1vTg00:Rj1uTg00M<j2\Tg00;2j1tTg00;Pk10<Tg00;nk10;Tg00N8j2`Tg00O>k10:Tg00<Yj2hTg00=<k208Tg00=^k207Tg00>8k204Tg00>dj3STg00?>k303Tg00?]k402Tg00oej4YTg00GUj1XTg00H:j25Tg00jPj2mTg00kQk500Tg00mHj2~Tg00moj2TTg00nKS00j2^Tg00oEj2bTg00T@j4]Tg00V3j3jTg00SBj4iTg00hnR0j2}Tg00nkR4j2rTg00dIj3qTg00O`j2|Tg00MZk401Tg00Tkj7{Tg00W:j7zTg00VVj8gTg00P`j6yTg00UOk605Tg010?k606Tg011kj7xTg00W^R5f0R7'?p=2g00X<R2/}7p=FAS275#Cp=Ef2R3f1R15S2/A7p=L1631/r7p=Pf3R8%Q3/51;q7p=H1531=q87p=GAS275p=41|31/579S28p=<1?531617'Ap=>16311?75'Ap=7AS217p=3P2P3P1P7H01p=KP2P1g00[@P7C]p=eP1g00YAR9g00Y`R:P:g00Z@R;P7g00Z`F{p=DP2P1g00[gP7C]p=[P3P9P:P:P;P1P7Fzp=ZP8P9P:P:P;P3P1P7Ggp=NP2f4R<P8P3P1P7Eyp=M1531/17p=J1617,A3p=IP2P1g00XZP7C]p=VP1P9P:P:P;P7J05p=_P1P9P:P:P;P7J06p=c15179S23p=Wf6R=P9P:P:P;f5R>P<P8P9P:P:P;P3P1P7GgGgp=RP3P9P:P:P;P1P7Fxp=f1A17,r3p=kg00\NS01#OS02#O#OR9#O#O#O#s#l%s9#l#w[S03Q031657S04B09831P4Ap<83%27R?1?78'AP>P<P7P8CU'AXg2#F%a9R9,1>R@10>9RA#ERB9L1@5P1f9RCf8RDP8P7CHX22#F[\?^_2P7Ap><8P611<99d=>10<9#Ef7REP=P@PACH[11E9RA10E9#ERF9L1A5P1f;RGf:RHP8P7CHX22#F[\?^_2RIP711=9RJ9dDEPHPC11D910D9RKCH\F11H9RF10H9RL#E9L1F5P1P411G9R4,6310G9#ERM9L34f?RNf>S05#QROP<P7CGX22#FP7f<RP/19RQ,68P2f@RR%QNRSP>P7CGX22P5P=P<f=RT/B9%2TS06%29RU10N9RV#2[[Q05/@9Q05#2S0711R9RW#2\U[19N9%49RX#CRYPRP9PW10R9RWC<RZ[1:R91659R[fAR\/09R]?>]9S08[1=\91695R^fBR_/09R`=79`[1;_9fCR`/19Ra#4\X18`9fDRb/09S09/3b\X11b9P2fERc/09S0:P2g00]3Rd#vS0;%udS0<1\23S0=%t2S0>7K1S0?&0<2S0@&0;2RdQ01,`2ReQ02,`2S0A'e,DdS0B&0::R:Pd1h25Rf/[e,DdS0CP:Q0CQ0B5ZdCNS0DCN208d;S0EP7P3g00]_R;g00^?Rg+0720473=S;gdB03251H02S0FbUbVbWX12X821671S0G%21S0H%23S0I1638S0J'A[[^12^82P7P3Q05PHPTO4bTb:b9b6b5b4b3b0b`b7O2CYWiP7O110P9Rg#E9L8QP611T9,3<10T9#EP\PRP=P7CHX22#FP711N9R;,3=%EW11\9Pc%QbRWP1P7CGX22#FX_2P2Pb%Q`Rh11_9P7CGX22P]PCP7O1CYPDP1DMWzWmP1P7O2n2001000000120000000W0P7O1n200100000021100010000WiXn?X_2WjWqP1P7O2n2001000000121000000W0P7O11?7<,A?P=P>P7P<CU'AXg2#FP0P21?7>,A?PEP=P7P>CU'AXg2PIP71?7E,A?PCPDP7PECU'AP6Q0H1?1D'APHPCP1PDCUAL14M9P14PNPOP8P7CGX22#F[\?^_2P7%28S0K1?8H'APTPPP<PGCUP6Q05?dT@PNPOPJ10=9CG\BQ01#XS0L#XS0M#aRB=J=9/?7AJTB9RJ7I7PRPSP1Q0M#X#X#X#O#O#aS0NCG[^f2'A%EV9L1;9P1;P`%Q_R;P8P7CGX22#F[\?^_2P7AdRNA%EKP_P\11C910C9RKCH[AJCB9/?7AJRB97I7P`P;P1Q0NCG[^f2'AP6%EKP`P;PFPLCG[AJHB9/?7AJ\B97I7PbPhP1Q0NCG[^f210`9Rh#E9L1a9P1afGRafFRL#QRFP8P7CGX22#F[\?^_2P7PcPWPQPgCG\M1?J7AJbB97I7PaPFP1Q0NCG[^f211L9S0OQ0O10L9RF#E5L15P11Ba9%2aRJfIRM/09Rg#2S0P\U[1B\9%2\%2h\U[1@M9%2MS0QfKRh/19S0R#2\U[1@`9%2`S0S11c9S0T#2\U[19b9PcP9Q0TQ0:C<\Y1:c9%2FS0U?IF9\[1=L910a9S0VQ0V579\^1;a9fHRQ/19S0W#4\X18Q913gM\X11M9S0XP2fJRW/09R;P2fRS0Y/99fSRKP911K9S0Z10K9S0[C<\Y1:K9fTRA/09S0\Q0\;>9\[1=A9fURV/09S0]Q0]579\^1;V9fVRS/19S0^#4\X18S9fWRO/09R@/3O\X11O9S0_P2fXRP/09S0`P2Q0Y/5BS0a/9915KBR4P91149S0b1049S0cC<\Y1:4915ABRI/09S0dQ0d;>9\[1=I915VBR0/09S0eQ0e579\^1;0915SBR]/19S0f#4\X18]915OBRi/09Rj/3i\X11i9S0gP215PBRk/09RlP2f`S0h/5BS0i/99faS0j/5BS0kP9Q0k/19S0lQ0k/09S0mC<\YQ0k/:9fbRm/5BRn/09S0nQ0n;>9\[1=n9fcRo/5BRp/09Rq=79q\^1;p9fdRr/5BRs/19S0o#4\X18s9feS0p/5BRt/09S0q/3t\X11t9S0rP2ffRu/5BRv/09RwP2Q0;Q0<Q0>Q0@1h29Rx/Vf,Dd,_dQ0EQ0FbUbVbWg00^_S0s\XP7bTS0tbQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b`b7bJbK9oR9PZ1BQ9%2Q%2;S0u\U[1B_9%2_S0vQ09#2\U[1@W9%2WS0wfLRZ/19S0x#2\U[1@b9%2bS0yQ0O#2\U[19c9PLP9Q0OPFC<\Y1:L9Q0V#2S0zQ0V;I9\[1=a910Q9RF=79F\^1;Q9Q0X#4\X18M913;W\X11W9RyP210h9RzP219K9PAP911A9S0{Q0\C<\Y1:A9Q0]#2S0|Q0];I9\[1=V910S9S0}Q0}579\^1;S9Q0_#4\X18O9Q0`/3P\X11P9S0~P2fYR{/09S10P21949PIP911I9S11Q0dC<\Y1:I9Q0eQ0e;>9\[1=0910]9R|=79|\^1;]9Q0g#4\X18i913lk\X11k9S12P215{BR}/09S13P2Q0k/99PnP911n9S14Q0nC<\Y1:n9A>qq9\[1=p910s9S15Q15579\^1;s9Q0r#4\X18t913wv\X11v9S16P2fgR~/5BS17/09S18P2Q0;Q0<Q0>Q0@1efx,DdQ0EQ0FbUbVbWP[P7bTS19bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b`b7bJbK9n\9Q081BM9Q0Q%2z\U[1B`9Q0SQ0:#2\U[1@h9%2hS0SfMRx/19S08#2\U[1@c9%2cS1:11a9S1;#2\U[19L9PaP9Q1;Q0VC<\Y1:a9A>FF9\[1=Q9A79gg\^1;M9%4y\X18W913zh\XQ0RP210Z9S1;P219A9PVP911V9S1<Q0]C<\Y1:V9Q0}Q0};>9\[1=S9A79@@\^1;O9Q0~#4\X18P9Q10/3{\X11{9S1=P2fZRy/09S1>P219I9S1?P0P91109S1@Q0eC<\YS0e1:09S1AA>||9\[S1B1=]9S1CA79jj\^S1D1;i9S1EQ12#4\XS1F18k9S1GQ13/3}\XS1H11}9S1IP215yBS1J/09S1KP219n9S1LPpP911p9S1MPqC<\YS1N1:p9S1OQ15Q15;>9\[S1P1=s9S1QQ0qQ0q579\^S1R1;t9S1SQ16#4\XS1T18v9S1UQ18Q17'3\XS1VQ17/19S1WP2fhS1X/5BS1Y/09S1ZP2P6Q1:16c9S1[PYfPRq16Q9S1\Q0tWSXRJP1P7O2n2001000000120000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b`b7bJbK9oM9PMP9Q0XPgC<S0t1BW9S1]Q0wQ1;#2\U[S0w1Bb9Q0yQ0U\U[1@Z9S0U%2ZfNRI/19S1^#2\U[S1_1@L9%2LQ0W#2\U[19a9PQP9Q0WPFC<\Y1:Q9Q0P?Ig9\[1=M9A79;;\^1;W9Q0R#4\X18h9Q1;/3Z\XQ0xP210x9S1;P219V9S0RPSP9Q0^Q0}C<\YS0^1:S9S0P%2@S1`?I@9\[S1a1=O9S1bQ0`Q0`579\^S1c1;P9S1dQ1=#4\XS1e18{9S1fQ1>/3y\XS1g11y9S1hP2f[Rg/09S1iP21909P]P9Q0fP|C<\Y1:]9A>jj9\[1=i9A79ll\^1;k9Q1I#4\X18}9Q1KQ1J'3\XQ1J/19S0fP215gBS1j/09S1kP219p9PsP9Q0oQ15C<\Y1:s9Q0qQ0q;>9\[1=t9A79ww\^1;v9Q1W#4\XQ17/89Q1ZQ1Y'3\XQ1Y/19S1lP2fiR|/5BS1m/09S1nP2P6Q1:Q1[P[fQR0Q1\Q19WSXRJP1P7O2n2001000000120000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b`b7bJbK9nW9Q0u?I;9S0u1Bh9Q0SQ1;#2\U[1Bc9Q1:Q0z\U[1@x9%2xfOR;/19S0z#2\U[1@a9Q0X#2\U\J19Q9Q0t\Y1:M9Q0u\[1=W9A79zz\^1;h9Q0x#4\X18Z9Q1;/3x\XQ08P210I9P219S9POP9Q0_P@C<\Y1:O9Q0`Q0`;>9\[1=P9Q10Q10579\^1;{9Q1h#4\X18y9Q1i/3g\X11g9P2f\Rz/09S08P219]9PiP9Q0gPjC<\Y1:i9A>ll9\[1=k9Q13Q13579\^1;}9Q0f#4\XQ1J/89Q1kQ1j'3\XQ1j/19S1jP215zBS1k/09P219s9PtP9Q0rQ0qC<\Y1:t9A>ww9\[1=v9Q18Q18579\^Q17/;9Q1l#4\XQ1Y/89Q1nQ1m'3\XQ1m/19S1JP2fjS0f/5BS13/09S1;P2P6Q07Q05/69S07Q0p#2Pq%2R16\9P6Q0Q16M9S0x%2|PSQ0S16Z9S0up-0RkQ0;Q0<1\21S0tQ0@PdQ0C1cd85ZdP:Q0CCNQ0EQ0FbUbVbWX12WZ1A?1Q0H[^12^ZkP7fmRlftRj'?PlP|O3bTWYWXP1P7O2n2001000000120000000WSWRP1P7O2n2001000000120000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b`b7bJbK,mbQ09#4R]AJcB9S09Q0T'3[%C]Q09Q0TQ01#aR]3W['AP6Q0:#4S0:AJLB9S09Q0O'3[Q0:#CQ09Q0O;W][PqP;PCP7CHX22#FP7Q0V#4AJQB9Q0W'3[%EFAJMB9Q0X;W][1Bq9%2qQ0Y/09#2\U[Q1]Q0wQ0Y/@9Q0Y#2Q0{#2\U[Q0UQ1_15xBRx/@9%2x15;BRx/19RF#2\U[15IB/99PxP9PF10x9C<\Y1:x915qBRx/09RF?>F9\[1=x9150BS1_/09Rx=79x\^Q1_/;9Q0a/19S0U#4\XQ0a/89Q0c/34\XQ0bP2Q0dP2Q0RQ0^Q0PQ1aQ1bQ1cQ1dQ1eQ1fQ1gQ1hP2Q1iP219o9PrP911r910r9S1hC<\Y1:r9Q0p/09S1gQ1g;>9\[Q0p/=910u9S1fQ1f579\^1;u911~9S1e#4\X18~9Q1X/09S1dQ1X'3\XQ1X/19P210|9S1cP2Q13/99fkS1b/5BS1aP9Q1a/19Q1a/09S0PC<\YQ1a/:9flS0^/5BS0R/09Rx?>x9\[Q0R/=915lBS0d/09S0bQ0b579\^Q0d/;9fnS0c/5BS0a/19S0w#4\XQ0a/89foS1]/5BS0X/09S0WQ0X'3\XQ0X/19P2fpS0V/5BS09/09S0OP2P6%2E16E9S0:frS0T#2PS%2C16H9P6Q0v16_9fvRS#2PzQ0yQ1[Q0;Q0<Q0tQ0@Pd1efe,DdP:Q0CCNQ0EQ0FbUbVbWX12Q04Q0H[^12P7fzRxfyRFO2bTWYWXP1P7O2n2001000000120000000WSWRP1P7O2n2001000000120000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b7bJbKb[b\,mq10q9#4S0yQ1_/19S1_1109S04'3[Q0y#CQ1_Q04;W]['AP61009S1_#4S0yQ0UQ0Y/19S0Y'3[Q0y#CQ0UQ0Y;W][PVPAQ05P7CHX22#FP7Q0[#4Q11Q0{'3[Q0\#EQ1@Q1<;W][PIPVP91BV9S0\%2VS11Q1`\U[S1`1B;9S0[%2;Q1_#2\U[S1_1@O9S0U%2OQ1=#2\U[S0y1@09S0H%20Q0Z#2\U[S0C1@}9S0t%2}Q1j#2\U[S1j1@49S0v%24Q1@#2\U[S01Q1?Q0eQ1AQ1BQ1CQ1DQ1EQ1FQ1GQ1HQ1IP2Q1KP2Q1LQ1NQ1OQ1PQ1QQ1RQ1SQ1TQ1UQ1VQ1WP2Q1ZP219m9S1oPoP911o9S1p10o9S1qC<\YS1r1:o9S1sQ1h#2S1tQ1h;I9\[S1u1=r9S1vQ1gQ1g579\^S1gQ0p/;9S1w11u9S1x#4\XS1y18u9S1z10~9S1{/3~\XS1|Q1eP2Q1dP2Q0V/99S1}fqR4P911491049C<\YS1~1:49S20Q0T/09R}?>}9\[S21Q0T/=9S22fsS23/09R}=79}\^S24Q23/;9S2511j9S26#4\XS2718j9S28fuR}/09S29/3}\XRO11}9S2:P210S9RAP2P6P?1679S2;P[PzQ0I1689S2<P6%2GS2=16G9S2>P[PmQ06Q07Q19WYWXP1P7O2n2001000000120000000WSWRP1P7O2n2001000000120000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b7bJbKb[b\b^Q0\Q1`Q0[Q1_Q0UQ0yQ0HQ0CQ0tQ1jQ0vQ01Q1?Q0eQ1AQ1BQ1CQ1DQ1EQ1FQ1GQ1HQ1IP2Q1KP2Q1LQ1NQ1OQ1PQ1QQ1RQ1SQ1TQ1UQ1VQ1WP2Q1ZP2Q1oQ1rQ1sQ1uQ1vQ1gQ1wQ1yQ1zQ1|Q1eP2Q1dP2Q1}Q1~Q20Q21Q22Q24Q25Q27Q28POQ2:P2PAP2P6P?Q2;fxRO,?4PzQ0IQ2<P6Q2=Q2>f|S2>,?}PmQ06Q07Q0;Q0<Q0?Q0@Pd1cd<S2=Q0A,[e,DdS285ZdP:Q28CNQ0EQ0FbUbVbWX12X82XZk1?71,A31?13[^12^82^ZkP7%2Fp+01AS27PFP}O4bTWYWXP1P7O2n2001000000120000000WSWRP1P7O2n2001000000120000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b7bJbKb[b\b^I00Q1^Q1<'?Q0z,~\Q0z,6\Q0z,T\'^Q0011q9R\,6_1T_\PgPyPbP7CHX22#FP7Q04,6`P2PzPgPcP7CHX22P5PWPb1B{9S0z%2{Q1i#2\U[S1^1BK9%2KQ0|\U[1@g9S0|%2gf]RK/19R\#2\U[S1<1@V9Q11Q0_#2\U[15KBRV/@9S11%2Vf_RV/5BR_/19S0_#2\U[S061@i9%2iQ1I#2\U[19P9P{P9Q1=Q10C<\Y1:{9Q1>Q1>;>9\[1=y9Q1iQ1i579\^1;g911z9#4\X18z910K9S1i/3K\XP\P2f^R\/09S1>P219_9Q0iP9Q0i/19R_Q0i/09C<\YQ0i/:9Q0mQ0m;>9\[Q0k/=9Q0nQ0n579\^1;n9Q1M#4\X18p9Q15/3s\XQ0oP2Q0qP2Q0d/99Q0aP9Q0wQ0a/09S0wC<\YQ0a/:9Q0WQ0W;>9\[Q0X/=9Q0OQ0O579\^Q09/;9154BRs/19#4\X18s9Q0T/5BRs/09/3s\X11s9P2Q23/5BRs/09P219j9P}P9Q2:Q29C<\Y1:}9A>AA9\[1=S9fwRn/09S2:Q2:579\^1;n911O9S0T#4\X18O910F9R{/3F\X11F9P210x9P2P6P?Q2;A>~~aQ0hQ0IQ2<P6Q0QQ0xQ1bQ1b;>hPuQ0SQ0uQ0;Q0<Q0=1\28RP1\2<S097K<7K1Q0@PdQ0BP:PdQ0M,`2S0M,[f,DdP:PdQ02#X,`2S02,[f,DdS0OP:Q0DCNFRQ0EQ0FbUbVbWX12X82X]2Xe2Q0G%2<RiQ0KAIi<>[\i[[^12^82^]2^e2P7PCPIP;Q1]PgP=P3Q0cO8bTWYWXP1P7O2n2001000000121000000WSWRP1P7O2n2001000000121000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b7bJbKb[b\b^O2CYW|P7O1Q04,T`Q0Y,bbQ0Y,3bRb%Cb'^Q00Q0Z,3cRc%CcP\PKPaP7CHX22#FP7Q0{,3LS0{Q0]/b5S0ZQ0]#4RL%CL'^S0]Q00Q0}#4S0}Q0}#CS0YQ0jQ0hPWP7CHX22#FP7%4@S04P2PmQ0j#QS0DPhP7CGX22Q0NPhPWQ0~1?7hS0X?Ih_Xh2Q0~/?WQ0_,6W1BV9S0W%2VQ0j/09R_#2\U[S0aQ0zQ1^Q0j/@9S0qQ0j#2Q1p#2\U[S0oQ0|Q1<1@p9S15%2pQ0r#2\U[S0rQ11Q0619\9S1MPVP911V9S0n10V9RpC<\YS0k1:V9S0mQ0h/09R@?>@9\[S10Q0h/=9S1IA79__\^S07Q0j/;9S0j11m9S25#4\XS2418m9S22Q1q/3o\XS1qQ1pP2Q1hP219t9S21PvP9Q16PwC<\YS161:v9S20Q18Q18;>9\[S18Q17/=9S17Q1ZQ1Z579\^S1ZQ1Y/;9S1~Q1J#4\XS1}Q1m/89S1eQ1;Q13'3\XS1|Q13/19S1zP2Q0PP219s9S1y15jBRsP911s910s9C<\YS1w1:s9S1g15}BRs/09Rw?>w9\[S1v1=s9S1u15SBRs/09Rw=79w\^S1s1;s9S1r15nBRw/19S1o#4\XS1W18w9S1V15OBRt/09RL/3t\XS1U11t9S1TP215FBS1S/09RcP219x9S1Rf{RbP911b9S1Q10b9S1PC<\YS1O1:b9S1NQ2>/09R`?>`9\[S1LQ2>/=9S1Kf}S1H/09RC=79C\^S1GQ1H/;9S1Hf~RC/19#4\XS1F18C9S1Ep+01@RC/09/3C\XS1D11C9S1CP2Q27/09S27P2P6P?Q2;1?alPuQ0IQ2<P6Q0QQ0x1?h4Q0^Q0SQ0uQ0fPyO113aIQ0;Q0<Q0>?K3PQ0>7K1S1BQ0@PdP2Q0Ag010cS1APeC],DdS0eP:PdQ0L#O,`2RC,[f,DdS0LP:Q28FRQ0EQ0FbUbVbWX12X82X]21T17Q0K1?38[[^12^82^]2P7PHPSPqPmPEO5bTbdWYWXP1P7O2n2001000000120000000WSWRP1P7O2n2001000000120000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b7bJbKb[b\b^S281bp5%4pRp%Cp'^Q00%4@R@%C@Q0l,6ZP7%4_R_Q2516I7Xh2S0l1Bm9S1?%2mQ1t\U[S1t1Bz9S01%2zQ1>#2\U[S0v1@r9S1j%2rQ1x#2\U[S0t1@\9S0C%2\Q0h/19#2\U[S0H1@v9S0y%2vQ1l#2\U[S1lQ0i/@9S0UQ0i#2Q14#2\U[S0iQ1X/99S1_P|P911|9RUQ1cC<\YS1c1:|9S0[Q0f/09Rv?>v9\[S1`Q0f/=9S0\Q1b/09R@=79@\^S19Q1b/;9S1bQ0^/19#4\XS2?Q0^/89S2@10l9/3l\XS2A11l9S2BP2Q0c/09S2CP2Q1Y/99S1YQ1mP9Q1JQ1nC<\YS1nQ1m/:9S1mQ1;Q1;;>9\[S1;Q13/=9S13Q0PQ0P579\^S1JQ1a/;9S1aQ0R/19#4\XS2DQ0R/89S0RQ0bQ0d'3\XS0bQ0d/19S0dP2Q0wP219s9S2EPwP9Q1o10w9C<\YS1o1:w9S2FA>LL9\[S2G1=t9S2HA79cc\^S2IQ1S/;9S1S15xBRt/19#4\XS2J18t9S2K15bBRt/09/3t\XS2L11t9S2MP2Q2>/5B/09S2>P219S9S2NPnP911n9RtQ2:C<\YS2:1:n9S2O10O9RL?>L9\[S2P1=O9S2QA79{{\^S2R1;F9S2S11x9#4\XS2T18x9S2UQ1P/3b\XRbQ1QP2P`P2P6Q1:Q1[Q0V/6aP|Q1\P6Pi16<9RF16jhQ1]%2=RwQ0:Q1XPyO113RIS1PQ0cP\O1S0c13QHRsQ0;Q0<Q0=Q0>9KP87K1Q0@PdQ02/Vf,DdRpP:PdQ0OP:PdQ0B1cd>1_dp5Zd5fdP:Q0BCNFRQ0EQ0FbUbVbWX12X82X]2XZk%43Q0KQ0J%4<Q0s[7k>168<[[[^12^82^]2^ZkP713x0PqP0PxPKPDPOO7bTbdbkWYWXP1P7O2n2001000000121000000WSXRJP1P7O2n2001000000121000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b7bJbKb[b\b^Q14Q05P7O1DMWcP7O1%C_Q25/5]Q0lQ1?Q1tQ01Q0vQ1jQ0tQ0CQ0HQ0yQ1lQ0UQ0iQ1_Q1cQ0[Q1`Q0\Q19Q1bQ2?Q2@Q2AQ2BP2Q2CP2Q1YQ1nQ1mQ1;Q13Q1JQ1aQ2DQ0RQ0bQ0dP2Q0wP2Q2EQ1oQ2FQ2GQ2HQ2IQ1SQ2JQ2KQ2LQ2MP2Q2>P2Q2NQ2:Q2OQ2PQ2QQ2RQ2SQ2TQ2UPbQ1QP2P`P2P6Q1:Q1[Q0V15a]R`'6P|Q1\P6PiPF15h]Rb,6jQ1]Q0:P~PyO115I]R_,3RS1]Q0cPsQ0;Q0<Q0?Q0@PdQ0BQ0A,Ve,DdQ2=5Zd5fdP:Q0A1h2]Rs5j2,ee,DdCNQ0EQ0FbUbVbWX12X82XZkRKQ0G1371;k3153],61[^12^82^ZkRpP7%EqP0PxPOO4bTbdblWYXXwP1P7O2n2001000000120000000WSXRJP1P7O2n2001000000121000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b7bJbKb[b\b^Q14PTP7O1DMWcP7O1n200110000021110411101baCiQ12PRP7O1RRDMO2CYWbP7O1Q04#CRTQ0~PoPmP1P7CHX22#FX_2P2PmQ0DQ1=P7CGX22Q0`PZP7O1CYPWP8DMWbP7O1n200110000021110410101baWmP7O1Q0{#CP2PVP\PQP7CHX22Q0NPQPaQ1@/?aQ1k/19,6aQ0ZQ0]Q00Q0}Q0YQ0g/?MP7Q04Q0~Q0XXh2RQQ28Q12PRDMWbP7O1Q0~/5]PQQ0WQ0aQ0zQ1^Q0qQ0oQ0|Q1<Q15Q0rQ11Q06Q1MQ0kQ0mQ10Q1IQ07Q0jQ24Q22Q1qQ1pP2Q1hP2Q21Q16Q20Q18Q17Q1ZQ1~Q1}Q1eQ1|Q1zP2Q0PP2Q1yQ1wQ1gQ1vQ1uQ1sQ1rQ1WQ1VQ1UQ1TP2PcP2Q1RQ1OQ1NQ1LQ1KQ1GQ1HQ1FQ1EQ1DQ1CP2Q27P2P6P?Q2;1?`lPuQ0IQ2<P6Q0QQ0x1?b4Q0^Q0SQ0uP|PyO113a_PnPgO1p+01Mp+01LP;PICHQ0;Q0<Q1BQ0@PdQ0A/Ve,Dd,_dP:PdQ0eP:PdQ0LP:Aj2esQ0A'[,DdCNFRQ0EQ0FbUbVbWX12X82X]21317Q0s[1T31158]/?<\i[[^12^82^]2P7PGPnP0Q0hPoPDO6bTbjbpWYWXP1P7O2n2001000000121000000WSWRP1P7O2n2001000000121000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b7bJbKb[b\b^Q12PNP7O1DMXbTP7O1n200110000021110411101baQ08/b5Q08#4R5%C5'^Q00Q1i#4R5%C5AJ\B9,6MP7Q1>#4RMQ0n16h7Xh2R\Q0WQ0aQ0zQ1^Q0qQ0oQ0|Q1<Q15Q0rQ11Q06Q0p/99RBPuP9Q1xQ1fC<\YR51:u9RTQ1{Q1{;>9\[RN1=~9R~Q1dQ1d579\^RoQ1X/;9R0%4U\XRU18|9R|Q0f,3v\XRvQ0f/19R<P2P@P2Q21Q16Q20Q18Q17Q1ZQ1~Q1}Q1eQ1|Q1zP2Q0PP2Q1yQ1wQ1gQ1vQ1uQ1sQ1rQ1WQ1VQ1UQ1TP2PcP2Q23/99RsPjP9Q2610j9C<\YRY1:j9RIQ29Q29;>9\[R[1=}9R}A79AA\^R^1;S9RA%4t\XRt18n9Rn13LO\XRXQ0TP2P{P2P6Q1:Q1[16laPuQ1\P6PiPF164hQ0^Q0:Q0pPyO1Q1PQ0;Q0<Q0>Q097K31\2>9KP>7K1Q0@Pd1VCf,DdRCP:PdQ0M,Ve,Dd,_dP:PdP2PeQ1AQ0MC],DdP:PdQ0LP:PdQ0OP:PdQ0B1cdE1_dC5Zd5fdP:Q0BFRFRFRQ0EQ0FbUbVbWX12X82X]2Xe2Xr2XZk%48131>Q0s[1T3=%4DQ0s[,AH9P>=16=E[\w\w[[[^12^82^]2^e2^r2^ZkP713SqPGP;PHPqPSPzPVPmPEP8PjO<bTbkWYXXwP1P7O2n2001000000121000000WSXRJP1P7O2n2001000000121000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b7bJbKb[b\b^Q0_PGP7O1DMWcP7O1%CMQ0n/5]P\Q0WQ0aQ0zQ1^Q0qQ0oQ0|Q1<Q15Q0rQ11Q06PBP5PTPNP~PoP0PUP|PvP<P2P@P2Q21Q16Q20Q18Q17Q1ZQ1~Q1}Q1eQ1|Q1zP2Q0PP2Q1yQ1wQ1gQ1vQ1uQ1sQ1rQ1WQ1VQ1UQ1TP2PcP2PsPYPIP[P}P^PAPtPnPXQ0TP2P{P2P6Q1:Q1[16l`PuQ1\P6PiPF164bQ0^Q0:PrPyO1Q1]PKPpP7%E;PqPSPjO4bTblWYXXwP1P7O2n2001000000120000000WSXRJP1P7O2n2001000000121000000bQbNbCbBbAb@b?bPbMb>b=b<b;bIbObLbHbGbFbEbDb:b9b6b5b4b3b0b7bJbKb[b\b^Q0_PHP7O1DMWcP7O1n200110000021110411101baCiO2CYW~P7O1n200110000021110411101baWxP7O1n200110000021110611105bab}WlWkP1P7O2n2001000000121000000b0WpWdP1P7O2n2001000000121000000b0c03bvc02buWiXn?X_2WwWjP1P7O2n2001000000121000000W0WqP1P7O2n2001000000121000000W0WyP1P7O2n2001000000121000000W0Xg2P1P7O2n2001000000121107000W0P7O1n200100000021100011000W0W{Xs2Xt2WoP3P1P7O3Xs2Xt2Woo"). Qed.

End ShadowRLawsB.
