(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg Hoare AsanAcct HeapIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition SB : Z := 0x7fff8000.
Definition S (a : Z) : Z := a / 8 + SB.
Definition BIGSHADOW_LO : Z := 0x7fff7000.
Definition BIGSHADOW_HI : Z := 0x10007fff8000.

Definition app_mem (a n : Z) : Prop := 0 <= a /\ (a + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= a) /\ a + n <= 2 ^ 47.

Record asan_layout : Type := AL {
  hl_segs      : list Segment;
  hl_malloc    : Z;
  hl_free      : Z;
  hl_aligned_alloc : Z;
  hl_stack_malloc : Z -> Z;
  hl_handle_no_return : Z;
  hl_asan_memset : Z; hl_asan_memcpy : Z; hl_asan_memmove : Z;
  hl_tp        : Z;
  hl_img_lo    : Z; hl_img_hi : Z;
  hl_rt_static : Z -> Prop;
  hl_rt_ro     : Z -> Prop;
  hl_scr_malloc : Z; hl_scr_free : Z; hl_scr_aligned : Z;
  hl_scr_stack_malloc : Z; hl_scr_no_return : Z; hl_scr_mem : Z;
  hl_k_per_malloc : Z; hl_b_lin : Z; hl_b_overhead : Z;
  hl_K0 : Z; hl_B0 : Z
}.

Record asan_run : Type := AR {
  ar_sptop : Z;
  ar_stack_top : Z; ar_stack_bottom : Z;
  ar_fs : Z;
  ar_space_beg : Z
}.
Abbreviation ahl_ceil ar := (ar_sptop ar - 8388608).

Definition app_rng (ar : asan_run) (a n : Z) : Prop :=
  0 <= a /\
  (a + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= a) /\ (a + n <= ar_sptop ar \/ a + n + 16 <= 2 ^ 47).
Definition FS_BYTES : Z := 0xb09000.

Definition acredit_ok (L : asan_layout) (cr : credit) (n : Z) : Prop :=
  hl_k_per_malloc L <= fst cr /\ hl_b_lin L * n + hl_b_overhead L <= snd cr.
Definition adebit (L : asan_layout) (cr : credit) (n : Z) : credit :=
  (fst cr - hl_k_per_malloc L, snd cr - (hl_b_lin L * n + hl_b_overhead L)).

Definition fframe : Type := (Z * Z * Z)%type.
Definition ff_addr (f : fframe) : Z := fst (fst f).
Definition ff_class (f : fframe) : Z := snd (fst f).
Definition ff_rs (f : fframe) : Z := snd f.
Definition ff_bytes (k : Z) : Z := 64 * 2 ^ k.

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

Definition ff_cap (k : Z) : Z := 2 ^ 20 / ff_bytes k.

Definition byte_at (M : word -> option byte) (a v : Z) : Prop := M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Definition shadow_zero (M : word -> option byte) (a g : Z) : Prop :=
  forall j, 0 <= j < g -> byte_at M (S a + j) 0.

Definition shadow_blk (M : word -> option byte) (u n : Z) : Prop :=
  shadow_zero M u (n / 8) /\ (n mod 8 <> 0 -> byte_at M (S u + n / 8) (n mod 8)).

Definition aacc (M : word -> option byte) (p n : Z) : Prop :=
  forall a, p <= a < p + n -> byte_at M (S a) 0 \/ (exists v, byte_at M (S a) v /\ 1 <= v <= 7 /\ a mod 8 < v).

Definition in_shadow_of (a n x : Z) : Prop := S a <= x <= S (a + n - 1).

Definition ablock_range (L : asan_layout) (ar : asan_run) (u n : Z) : Prop :=
  4096 <= u /\ (u + n <= hl_img_lo L \/ hl_img_hi L <= u) /\ u mod 16 = 0 /\ 0 < n /\ u + n <= ahl_ceil ar /\ app_mem u n.
Definition fframes_apart (a n : Z) (FF : list fframe) : Prop :=
  forall f, In f FF -> a + n <= ff_addr f \/ ff_addr f + ff_bytes (ff_class f) <= a.

Definition block_shadow (LB : list (Z * Z)) (a : Z) : Prop := exists b, In b LB /\ in_shadow_of (fst b) (snd b) a.
Definition aclient_g (BS : Z -> Z -> Z -> Prop) (ST : Z -> Prop) (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scratch : Z) (a : Z) : Prop :=
  in_block LB a
  \/ (ahl_ceil ar <= a < 2 ^ 47 /\ ~ (sp - scratch <= a < sp))
  \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ ST a)
  \/ in_fframe FF a
  \/ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a
  \/ (exists f, In f FF /\ in_shadow_of (ff_addr f) (ff_bytes (ff_class f)) a)
  \/ (exists b, In b LB /\ BS (fst b) (snd b) a).
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

Definition astack_ok (L : asan_layout) (ar : asan_run) (M : word -> option byte) (scratch sp : Z) : Prop :=
  sp mod 16 = 0 /\ ahl_ceil ar + 4096 + scratch <= sp /\ sp <= ar_sptop ar /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\
  (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= scratch -> store_ok (hl_segs L) M (Z_to_bv 64 (sp - scratch + d)) m = true) /\
  defined M sp (ar_stack_top ar - sp).

Definition model_rt (m m' : Model) : Prop :=
  m' = mkModelOf (m_fd m) (m_vm m') (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).

Definition vml : Type := (VmMaps * list (word * word))%type.
Definition vml_of (m : Model) : vml := (m_vmmaps m, m_vm_lazy m).

Definition shadow_allowed (A : list (Z * Z)) (a n : Z) : Prop :=
  forall x, in_shadow_of a n x -> page_allowedb A (page_base (Z_to_bv 64 x)) = true.

Definition ahid (A : list (Z * Z)) (m : Model) : word -> bool := mkH (m_vm_lazy m) A.

Record asan_statics_cells : Type := ASC {
  asc_got_lo : Z; asc_got_hi : Z;
  asc_cells : list (Z * Z * Z)
}.

Definition cell_is (segs : list Segment) (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Definition asan_statics (segs : list Segment) (C : asan_statics_cells) (M : word -> option byte) : Prop :=
  (forall a, asc_got_lo C <= a < asc_got_hi C -> M (Z_to_bv 64 a) = None)
  /\ Forall (fun c => cell_is segs M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) (asc_cells C).

Section AIface.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.

Record asan_iface : Type := AI {
  ri_inv : list (Z * Z) -> list fframe -> list fframe -> credit -> list (Z * Z) -> (word -> option byte) -> vml -> Prop
}.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

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
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= 4096 -> n mod 16 = 0 -> acredit_ok L cr n ->
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

Definition ff_room (k : Z) (FF LK : list fframe) : Prop := Z.of_nat (ff_count k (FF ++ LK)) + 2 <= ff_cap k.

Definition astack_malloc_spec (k : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_stack_malloc L) sp ->
    ff_room k FF LK ->
    (forall f, In f FF -> sp + 32 <= ff_rs f) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (F fl : Z) (LK' : list fframe),
        getr R' 10%bv = Z_to_bv 64 F ->
        regs_preserved R R' ->
        ar_fs ar <= F /\ F + ff_bytes k <= ar_fs ar + FS_BYTES /\ F mod ff_bytes k = 0 /\ app_mem F (ff_bytes k) /\ F + ff_bytes k <= ahl_ceil ar ->
        (F + ff_bytes k <= hl_img_lo L \/ hl_img_hi L <= F) ->
        fframes_apart F (ff_bytes k) (FF ++ LK') -> (forall b, In b LB -> F + ff_bytes k <= fst b \/ fst b + snd b <= F) ->
        incl LK' LK ->
        defined M' F (ff_bytes k) ->
        cell_is (hl_segs L) M' (F + ff_bytes k - 8) 8 fl ->
        ar_fs ar <= fl < ar_fs ar + FS_BYTES -> ~ aclient L ar LB ((F, k, sp + 32) :: FF) 0 0 fl ->
        (F + ff_bytes k <= fl \/ fl + 1 <= F) ->
        store_ok (hl_segs L) M' (Z_to_bv 64 fl) 1 = true ->
        shadow_zero M' F (ff_bytes k / 8) ->
        aheap_pres L ar LB FF sp (hl_scr_stack_malloc L) M M' ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB ((F, k, sp + 32) :: FF) LK' cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_stack_malloc L k)) M model) K.

Definition rt_release_frame : Prop :=
  forall LB FF LK cr A M M' V F k rs fl,
    ri_inv HI LB FF LK cr A M V -> In (F, k, rs) FF -> cell_is (hl_segs L) M (F + ff_bytes k - 8) 8 fl ->
    (forall a, 0 <= a < 2 ^ 64 -> a <> fl -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) \/ aclientw L ar LB FF 0 0 a) ->
    cell_is (hl_segs L) M' fl 1 0 -> (forall a : word, M a <> None -> M' a <> None) ->
    ri_inv HI LB (ff_remove F FF) LK cr A M' V.

Definition rt_flagptr : Prop :=
  forall LB FF LK cr A M V LB' FF' LK' cr' A' M' V' F k rs rs' fl,
    ri_inv HI LB FF LK cr A M V -> ri_inv HI LB' FF' LK' cr' A' M' V' ->
    In (F, k, rs) FF -> In (F, k, rs') FF' ->
    cell_is (hl_segs L) M (F + ff_bytes k - 8) 8 fl -> cell_is (hl_segs L) M' (F + ff_bytes k - 8) 8 fl.

Definition rt_leak_frames : Prop :=
  forall LB FF LK cr A M V FX,
    ri_inv HI LB FF LK cr A M V -> incl FX FF -> NoDup (map ff_addr FX) ->
    ri_inv HI LB (filter (fun f => negb (existsb (fun g => Z.eqb (ff_addr g) (ff_addr f)) FX)) FF) (FX ++ LK) cr A M V.

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
        sp - hl_scr_no_return L - 4096 <= lo <= sp -> lo mod 4096 = 0 ->
        shadow_zero M' lo ((ar_stack_top ar - lo) / 8) ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp (hl_scr_no_return L) a ->
                   ~ in_shadow_of lo (ar_stack_top ar - lo) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - hl_scr_no_return L <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_handle_no_return L)) M model) K.

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
  aacc M dst n /\ (forall i, 0 <= i < n -> aclientw L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (dst + i)) /\
  (forall i (m : nat), 0 <= i -> i + Z.of_nat m <= n -> store_ok (hl_segs L) M (Z_to_bv 64 (dst + i)) m = true) /\
  K [] /\ app_rng ar dst n.

Definition amemset_spec : Prop :=
  forall fx R M model LB FF LK cr A dst c n K,
    amem_pre fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 c ->
    amem_post fx R M model LB FF LK cr A dst n (fun _ v => v = c mod 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (hl_asan_memset L)) M model) K.

Definition amemcpy_spec_at (pc : Z) (may_overlap : bool) : Prop :=
  forall fx R M model LB FF LK cr A dst src n (bs : list byte) K,
    amem_pre fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 src ->
    aacc M src n -> 0 <= src /\ src + n <= 2 ^ 47 -> app_rng ar src n ->
    (forall i, 0 <= i < n -> hl_img_lo L <= src + i < hl_img_hi L \/ aclient L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (src + i)) ->

    rdn (hl_segs L) M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
    (may_overlap = false -> dst + n <= src \/ src + n <= dst) ->
    amem_post fx R M model LB FF LK cr A dst n (fun i v => nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.
Definition amemcpy_spec : Prop := amemcpy_spec_at (hl_asan_memcpy L) false.
Definition amemmove_spec : Prop := amemcpy_spec_at (hl_asan_memmove L) false.

Definition art_private (LB : list (Z * Z)) (FF : list fframe) (a : Z) : Prop :=
  ~ aclient L ar LB FF 0 0 a \/ hl_rt_ro L a \/ block_shadow LB a.

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
                       /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b))
    /\ (forall f, In f FF -> ar_fs ar <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs ar + FS_BYTES
                       /\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) [1; 2; 3]
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

Definition rt_small_high : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V -> forall b, In b LB -> snd b <= 4096 -> BIGSHADOW_HI <= fst b.

Definition rt_statics : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V -> asan_statics (hl_segs L) C M.

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
  aio_flagptr : rt_flagptr;
  aio_small_high : rt_small_high
}.
End AIface.

