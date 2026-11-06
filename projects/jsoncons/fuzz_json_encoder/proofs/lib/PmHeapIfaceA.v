(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg Hoare AsanAcct HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Export HeapIfaceA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition PM_FS_CLASSES : list Z := [0; 1; 2; 3; 4; 5].
Lemma pm_fs_classes_range : forall k, In k PM_FS_CLASSES <-> (0 <= k <= 5).
Proof. intros k. unfold PM_FS_CLASSES. cbn [In]. lia. Qed.

(* [comment removed for export] *)
Definition CONT_OOB : Z := 0xfc.
Definition shadow_cont (M : word -> option byte) (u n mid : Z) : Prop :=
  shadow_zero M u (mid / 8) /\ (mid mod 8 <> 0 -> byte_at M (S u + mid / 8) (mid mod 8))
  /\ (forall j, (mid + 7) / 8 <= j < (n + 7) / 8 -> byte_at M (S u + j) CONT_OOB).
Lemma shadow_blk_cont : forall M u n, shadow_blk M u n -> shadow_cont M u n n.
Proof. intros M u n (Z0 & PT). split; [exact Z0|]. split; [exact PT|]. intros j Hj. lia. Qed.
Definition shadow_blk_w (M : word -> option byte) (u n : Z) : Prop := exists mid, 0 <= mid <= n /\ shadow_cont M u n mid.
Lemma shadow_blk_w_of : forall M u n, 0 <= n -> shadow_blk M u n -> shadow_blk_w M u n.
Proof. intros M u n Hn H. exists n. split; [lia | exact (shadow_blk_cont M u n H)]. Qed.

(* [comment removed for export] *)
Definition FS_AFTER_RETURN : Z := 0xf5.

(* [comment removed for export] *)
Record asan_layout_x : Type := ALX {
  hlx_stack_free : Z -> Z;            (* [comment removed for export] *)
  hlx_sfree_pat : Z                   (* [comment removed for export] *)
}.

Section AIfaceX.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

(* [comment removed for export] *)
Definition rt_wf : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    (forall b, In b LB -> ablock_range L ar (fst b) (snd b) /\ defined M (fst b) (snd b) /\ shadow_blk_w M (fst b) (snd b)     (* [comment removed for export] *)
                       /\ shadow_allowed A (fst b) (snd b)
                       /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB) /\ fframes_apart (fst b) (snd b) (FF ++ LK)
                       /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b))
    /\ (forall f, In f FF -> ar_fs ar <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs ar + FS_BYTES
                       /\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) PM_FS_CLASSES
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
Definition astack_free_spec (pc pat k : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (F rs : Z) (K : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    In (F, k, rs) FF -> getr R 10%bv = Z_to_bv 64 F ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_stack_malloc L) sp ->
    (forall a, pat <= a < pat + 8 -> M (Z_to_bv 64 a) = None) ->                                  (* [comment removed for export] *)
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        (forall j, 0 <= j < ff_bytes k / 8 -> byte_at M' (S F + j) FS_AFTER_RETURN) ->           (* [comment removed for export] *)
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp (hl_scr_stack_malloc L) a ->
                   ~ in_shadow_of F (ff_bytes k) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->  (* [comment removed for export] *)
        (forall a, sp - hl_scr_stack_malloc L <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB (ff_remove F FF) LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') K) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.

(* [comment removed for export] *)
Record asan_iface_ok : Prop := AIOK {
  aio_malloc : amalloc_spec L ar scfg HI;
  aio_aligned : aaligned16_spec L ar scfg HI;
  aio_free : afree_spec L ar scfg HI;
  aio_stack_malloc : forall k, In k PM_FS_CLASSES -> astack_malloc_spec L ar scfg HI k;
  aio_release : rt_release_frame L ar HI;
  aio_leak : rt_leak_frames HI;
  aio_no_return : ahandle_no_return_spec L ar scfg HI;
  aio_memset : amemset_spec L ar scfg HI;
  aio_memcpy : amemcpy_spec L ar scfg HI;
  aio_memmove : amemmove_spec L ar scfg HI;
  aio_frame : rt_frame L ar HI;
  aio_wf : rt_wf;
  aio_lazy : rt_lazy L ar HI;
  aio_perm : rt_perm HI;
  aio_statics : rt_statics L C HI;
  aio_flagptr : rt_flagptr L HI;
  aio_small_high : rt_small_high HI
}.
End AIfaceX.

(* [comment removed for export] *)
Record pm_asan_iface_ok (L : asan_layout) (LX : asan_layout_x) (ar : asan_run) (C : asan_statics_cells) (scfg : SpuriousCfg) (HI : asan_iface) : Prop := PAIOK {
  pio_base : asan_iface_ok L ar C scfg HI;
  pio_stack_free5 : astack_free_spec L ar scfg HI (hlx_stack_free LX 5) (hlx_sfree_pat LX) 5
}.
