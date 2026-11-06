(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg Hoare AsanAcct HeapIface HeapIfaceA PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Export IcptIfaceA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record icpt_layout_x : Type := ICLX {
  iclx_memcmp : Z;
  iclx_scr_memcmp : Z;
  iclx_cxa_atexit : Z;
  iclx_scr_cxa : Z;
  iclx_atexit_tab : Z;
  iclx_atcxa : Z;
  iclx_scr_handler : Z;
  iclx_annotate : Z;
  iclx_need_locks : Z;
  iclx_memcmp2 : Z;
  iclx_memset : Z;
  iclx_setsh00 : Z;
  iclx_setshf5 : Z;
  iclx_setshf8 : Z;
  iclx_scr_setsh : Z
}.

Definition ATEXIT_TAB_BYTES : Z := 544.
Definition atexit_state_at (segs : list Segment) (AX : Z) (M : word -> option byte) (hs : list (Z * Z)) : Prop :=
  cell_is segs M AX 1 0
  /\ cell_is segs M (AX + 4) 4 0
  /\ match hs with
     | [] => cell_is segs M (AX + 8) 4 0 /\ (cell_is segs M (AX + 16) 8 0 \/ cell_is segs M (AX + 16) 8 (AX + 24) /\ cell_is segs M (AX + 24) 8 0)
     | _ => Z.of_nat (length hs) <= 32
            /\ cell_is segs M (AX + 16) 8 (AX + 24)
            /\ cell_is segs M (AX + 8) 4 (Z.of_nat (length hs))
            /\ cell_is segs M (AX + 24) 8 0
            /\ (forall i f a, nth_error hs i = Some (f, a) ->
                  cell_is segs M (AX + 32 + 8 * Z.of_nat i) 8 f /\ cell_is segs M (AX + 288 + 8 * Z.of_nat i) 8 a)
     end.

Fixpoint memcmp_val (b1 b2 : list byte) : Z :=
  match b1, b2 with
  | x :: r1, y :: r2 => if Z.eqb (bv_unsigned x) (bv_unsigned y) then memcmp_val r1 r2 else bv_unsigned x - bv_unsigned y
  | _, _ => 0
  end.

Section IIfaceX.
Variable L : asan_layout.
Variable ar : asan_run.
Variable IL : icpt_layout.
Variable ILX : icpt_layout_x.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

Definition amemcmp_spec_at (pc scr0 : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (p q n : Z) (b1 b2 : list byte) (Kt : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 q -> getr R 12%bv = Z_to_bv 64 n -> 0 <= n <= 2 ^ 27 ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (scr0) sp ->
    0 <= p -> p + n <= 2 ^ 47 -> 0 <= q -> q + n <= 2 ^ 47 ->
    rdn (hl_segs L) M (Z_to_bv 64 p) (Z.to_nat n) = Some b1 -> rdn (hl_segs L) M (Z_to_bv 64 q) (Z.to_nat n) = Some b2 ->
    (forall i, 0 <= i < n -> hl_img_lo L <= p + i < hl_img_hi L \/ aclient L ar LB FF sp (scr0) (p + i)) ->
    (forall i, 0 <= i < n -> hl_img_lo L <= q + i < hl_img_hi L \/ aclient L ar LB FF sp (scr0) (q + i)) ->
    aacc M p n -> aacc M q n -> app_rng ar p n -> app_rng ar q n ->
    Kt [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        getr R' 10%bv = Z_to_bv 64 (memcmp_val b1 b2) -> regs_preserved R R' ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp (scr0) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - scr0 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') Kt) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) Kt.

Definition amemcmp_spec : Prop := amemcmp_spec_at (iclx_memcmp ILX) (iclx_scr_memcmp ILX).

Definition amemset_spec_at (pc : Z) : Prop :=
  forall fx R M model LB FF LK cr A dst c n K,
    amem_pre L ar HI fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 c ->
    amem_post L ar scfg HI fx R M model LB FF LK cr A dst n (fun _ v => v = c mod 256) K ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) K.
Definition amemset_libc_spec : Prop := amemset_spec_at (iclx_memset ILX).

Definition aset_shadow_spec (pc v scr : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (f : fframe) (sa n : Z) (Kt : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 sa -> getr R 11%bv = Z_to_bv 64 n ->
    In f FF -> 0 <= n -> S (ff_addr f) <= sa -> sa + n <= S (ff_addr f) + ff_bytes (ff_class f) / 8 ->
    Hoare.ret_ok (getr R 1%bv) -> astack_ok L ar M scr sp -> Kt [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        (forall j, 0 <= j < n -> byte_at M' (sa + j) v) ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> ~ (sa <= a < sa + n) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - scr <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') Kt) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) Kt.

Definition acxa_atexit_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (f arg dso : Z) (hs : list (Z * Z)) (Kt : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    let AX := iclx_atexit_tab ILX in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 f -> getr R 11%bv = Z_to_bv 64 arg -> getr R 12%bv = Z_to_bv 64 dso ->
    0 <= f < 2 ^ 64 -> 0 <= arg < 2 ^ 64 ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (iclx_scr_cxa ILX) sp ->
    atexit_state_at (hl_segs L) AX M hs -> Z.of_nat (length hs) + 2 <= 32 ->
    hs <> [] ->
    cell_is (hl_segs L) M (iclx_need_locks ILX) 1 0 ->
    (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= ATEXIT_TAB_BYTES -> store_ok (hl_segs L) M (Z_to_bv 64 (AX + d)) m = true) ->
    Kt [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        getr R' 10%bv = Z_to_bv 64 0 -> regs_preserved R R' ->
        atexit_state_at (hl_segs L) AX M' (hs ++ [(f, arg); (iclx_atcxa ILX, 0)]) ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp (iclx_scr_cxa ILX) a -> ~ (AX <= a < AX + ATEXIT_TAB_BYTES) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - iclx_scr_cxa ILX <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') Kt) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 (iclx_cxa_atexit ILX)) M model) Kt.

Definition ahandler_spec (f a : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (Kt : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 a ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (iclx_scr_handler ILX) sp ->
    Kt [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        (forall a', 0 <= a' < 2 ^ 64 -> aclient L ar LB FF sp (iclx_scr_handler ILX) a' -> M' (Z_to_bv 64 a') = M (Z_to_bv 64 a')) ->
        (forall a', sp - iclx_scr_handler ILX <= a' < sp -> M' (Z_to_bv 64 a') <> None) ->
        (forall a' : word, M a' <> None -> M' a' <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') Kt) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 f) M model) Kt.

Definition aannotate_spec (pc scr : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (u n om nm : Z) (Kt : ShapeAlg.TSet),
    let sp := bv_unsigned (getr R 2%bv) in
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    In (u, n) LB -> getr R 10%bv = Z_to_bv 64 u -> getr R 11%bv = Z_to_bv 64 (u + n) -> getr R 12%bv = Z_to_bv 64 (u + om) -> getr R 13%bv = Z_to_bv 64 (u + nm) ->
    0 <= om <= n -> 0 <= nm <= n -> n <= 2 ^ 18 ->
    shadow_cont M u n om ->
    Hoare.ret_ok (getr R 1%bv) -> astack_ok L ar M scr sp -> Kt [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' -> shadow_cont M' u n nm ->
        (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> ~ in_shadow_of u n a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, sp - scr <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
        (forall a : word, M a <> None -> M' a <> None) ->
        model_rt model model' -> MInv A model' ->
        ri_inv HI LB FF LK cr A M' (vml_of model') ->
        srealizes (hl_segs L) scfg (cfg_at fx R' (getr R 1%bv) M' model') Kt) ->
    srealizes (hl_segs L) scfg (cfg_at fx R (Z_to_bv 64 pc) M model) Kt.

Record pm_aicpt_ok (ANNOTATE : Prop) : Prop := PAICOK {
  pic_strlen : astrlen_spec L ar IL scfg HI;
  pic_globals : rt_globals IL HI;
  pic_img_shadow : rt_img_shadow L IL HI;
  pic_shadow_defined : rt_shadow_defined HI;
  pic_tls : rt_tls L ar IL HI;
  pic_memcpy_libc : amemcpy_libc_spec L ar IL scfg HI;
  pic_memmove_libc : amemmove_libc_spec L ar IL scfg HI;
  pic_memcmp : amemcmp_spec;
  pic_cxa_atexit : acxa_atexit_spec;
  pic_annotate : ANNOTATE;
  pic_atcxa : ahandler_spec (iclx_atcxa ILX) 0;
  pic_memcmp2 : amemcmp_spec_at (iclx_memcmp2 ILX) (iclx_scr_memcmp ILX);
  pic_memset_libc : amemset_libc_spec;
  pic_setsh00 : aset_shadow_spec (iclx_setsh00 ILX) 0 (iclx_scr_setsh ILX);
  pic_setshf5 : aset_shadow_spec (iclx_setshf5 ILX) 245 (iclx_scr_setsh ILX);
  pic_setshf8 : aset_shadow_spec (iclx_setshf8 ILX) 248 (iclx_scr_setsh ILX)
}.
End IIfaceX.
