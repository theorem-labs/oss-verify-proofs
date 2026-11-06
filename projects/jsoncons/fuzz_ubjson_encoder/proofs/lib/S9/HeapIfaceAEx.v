(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull L5Defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Definition ann_shadow (M : word -> option byte) (b u c : Z) : Prop :=
  shadow_zero M b (u / 8) /\ (u mod 8 <> 0 -> byte_at M (S b + u / 8) (u mod 8))
  /\ (forall j, (u + 7) / 8 <= j < (c + 7) / 8 -> byte_at M (S b + j) 252).

Definition shadow_blkR (M : word -> option byte) (u n : Z) : Prop :=
  shadow_blk M u n \/ (exists m, 0 <= m <= n /\ ann_shadow M u m n).

Lemma shadow_blkR_of (M : word -> option byte) u n : shadow_blk M u n -> shadow_blkR M u n.
Proof. intros H. left. exact H. Qed.

Lemma ann_shadow_full (M : word -> option byte) b c : 0 <= c -> ann_shadow M b c c <-> shadow_blk M b c.
Proof.
  intros Hc. unfold ann_shadow, shadow_blk. split.
  - intros (Z0 & P & _). split; [exact Z0 | exact P].
  - intros (Z0 & P). split; [exact Z0 | split; [exact P | intros j Hj; lia]].
Qed.

Definition atexit_cells (segs : list Segment) (M : word -> option byte) (X f0 a0 f1 a1 atc : Z) (hs : list (Z * Z)) : Prop :=
  L5.u8_at segs M X 0 /\ L5.u32_at segs M (X + 4) 0 /\ L5.u32_at segs M (X + 8) (2 + 2 * Z.of_nat (length hs))
  /\ L5.u64_at segs M (X + 16) (X + 24) /\ L5.u64_at segs M (X + 24) 0
  /\ L5.u64_at segs M (X + 32) f0 /\ L5.u64_at segs M (X + 288) a0
  /\ L5.u64_at segs M (X + 40) f1 /\ L5.u64_at segs M (X + 296) a1
  /\ (forall (i : nat) f a, nth_error hs i = Some (f, a) ->
        L5.u64_at segs M (X + 48 + 16 * Z.of_nat i) f /\ L5.u64_at segs M (X + 56 + 16 * Z.of_nat i) atc
        /\ L5.u64_at segs M (X + 304 + 16 * Z.of_nat i) a /\ L5.u64_at segs M (X + 312 + 16 * Z.of_nat i) 0).

Record ext_consts : Type := EXTC {
  ec_ann_pc : Z; ec_ann_scr : Z;
  ec_cxa_pc : Z; ec_cxa_scr : Z;
  ec_atexit : Z; ec_f0 : Z; ec_a0 : Z;
  ec_f1 : Z; ec_a1 : Z;
  ec_atc : Z;
  ec_nl : Z;
  ec_sf_pc : Z; ec_sf_scr : Z
}.

Section X.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

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

Record asan_iface_okR : Prop := AIOKR {
  aior_malloc : amalloc_spec L ar scfg HI;
  aior_aligned : aaligned16_spec L ar scfg HI;
  aior_free : afree_spec L ar scfg HI;
  aior_stack_malloc : forall k, In k [0; 1; 2; 3; 5] -> astack_malloc_spec L ar scfg HI k;
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

Definition astack_free_spec (pc scr k : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet) (F rs : Z),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    In (F, k, rs) FF ->
    getr R 10%bv = Z_to_bv 64 F ->
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

Definition rt_frame_ctr : Prop :=
  forall LB FF LK cr A M M' V, ri_inv HI LB FF LK cr A M V ->
    (forall a, 0 <= a < 2 ^ 64 -> art_private L ar LB FF a -> ~ (hl_tp L + 16 <= a < hl_tp L + 20) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    cell_is (hl_segs L) M' (hl_tp L + 16) 4 0 -> (forall a : word, M a <> None -> M' a <> None) -> ri_inv HI LB FF LK cr A M' V.

Record asan_ext_ok (E : ext_consts) : Prop := AEXT {
  aex_annotate : annotate_spec (ec_ann_pc E) (ec_ann_scr E);
  aex_cxa_atexit : cxa_atexit_spec (ec_cxa_pc E) (ec_cxa_scr E) (ec_atexit E) (ec_f0 E) (ec_a0 E) (ec_f1 E) (ec_a1 E) (ec_atc E) (ec_nl E);
  aex_frame_ctr : rt_frame_ctr;
  aex_free_null : afree_null_spec L ar scfg HI;
  aex_stack_free : astack_free_spec (ec_sf_pc E) (ec_sf_scr E) 5
}.
End X.

Definition strict_of (HIR : asan_iface) : asan_iface :=
  AI (fun LB FF LK cr A M V => ri_inv HIR LB FF LK cr A M V /\ Forall (fun b => shadow_blk M (fst b) (snd b)) LB
                               /\ Forall (fun f => In (ff_class f) [1; 2; 3]) (FF ++ LK)).

End HAJ.
