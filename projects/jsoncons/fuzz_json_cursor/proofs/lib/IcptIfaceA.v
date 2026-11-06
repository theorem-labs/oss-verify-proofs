(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg Hoare AsanAcct HeapIface HeapIfaceA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record icpt_layout : Type := ICL {
  icl_strlen : Z;
  icl_scr_strlen : Z;
  icl_ro_lo : Z; icl_ro_hi : Z;
  icl_globals : list (Z * Z);
  icl_poison : list (Z * Z);

  icl_memcpy : Z;
  icl_memmove : Z;
  icl_ctxslot : Z;

  icl_strerror_r : Z;
  icl_scr_strerror : Z;
  icl_strerror_cells : list (Z * Z * Z);

  icl_sro_lo : Z; icl_sro_hi : Z
}.

Definition EINVAL_MSG : list Z := [73; 110; 118; 97; 108; 105; 100; 32; 97; 114; 103; 117; 109; 101; 110; 116; 0].

Section IIface.
Variable L : asan_layout.
Variable ar : asan_run.
Variable IL : icpt_layout.
Variable scfg : SpuriousCfg.
Variable HI : asan_iface.

Let cfg_at (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R pc M (seg_rom (hl_segs L))) model.

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
    aacc M s (K + 1) -> app_rng ar s (K + 1) ->
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

Definition rt_globals : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    Forall (fun g => shadow_blk M (fst g) (snd g) /\ shadow_allowed A (fst g) (snd g)) (icl_globals IL).

Definition rt_img_shadow : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    forall a n, hl_img_lo L <= a -> a + n <= hl_img_hi L -> 0 < n -> Forall (fun r => a + n <= fst r \/ snd r <= a) (icl_poison IL) ->
      (forall x, in_shadow_of a n x -> byte_at M x 0) /\ shadow_allowed A a n.

Definition LOWSH_LO : Z := 0x7fff8000.      Definition LOWSH_HI : Z := 0x8fff7000.
Definition HIGHSH_LO : Z := 0x2008fff7000.  Definition HIGHSH_HI : Z := 0x10007fff8000.
Definition rt_shadow_defined : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    forall x, (LOWSH_LO <= x < LOWSH_HI \/ HIGHSH_LO <= x < HIGHSH_HI) -> M (Z_to_bv 64 x) <> None.

Definition rt_tls : Prop :=
  forall LB FF LK cr A M model, ri_inv HI LB FF LK cr A M (vml_of model) ->
    exists ctx th tbv tev blk : Z,
      cell_is (hl_segs L) M (icl_ctxslot IL) 8 ctx /\ cell_is (hl_segs L) M (ctx + 152) 8 th /\
      cell_is (hl_segs L) M (th + 48) 8 tbv /\ cell_is (hl_segs L) M (th + 56) 8 tev /\
      cell_is (hl_segs L) M (hl_tp L + 8) 8 blk /\ cell_is (hl_segs L) M (blk + 24) 8 (hl_tp L) /\
      4096 <= ctx /\ ctx + 160 <= ahl_ceil ar /\ 4096 <= th /\ th + 64 <= ahl_ceil ar /\ 4096 <= blk /\ blk + 4096 <= ahl_ceil ar /\
      0 <= tbv < 2 ^ 64 /\ 0 <= tev < 2 ^ 64 /\
      (ctx + 160 <= hl_img_lo L \/ hl_img_hi L <= ctx) /\ (th + 64 <= hl_img_lo L \/ hl_img_hi L <= th) /\ (blk + 4096 <= hl_img_lo L \/ hl_img_hi L <= blk) /\

      (ctx + 160 <= th \/ th + 64 <= ctx) /\ (ctx + 160 <= blk \/ blk + 4096 <= ctx) /\ (th + 64 <= blk \/ blk + 4096 <= th) /\
      (forall a, ctx <= a < ctx + 160 \/ th <= a < th + 64 \/ blk <= a < blk + 4096 ->
                 (forall sp scr, ~ aclient L ar LB FF sp scr a) /\
                 page_in_ranges (page_base (Z_to_bv 64 a)) (m_vm_lazy model) = false).

Definition amemcpy_libc_spec : Prop := amemcpy_spec_at L ar scfg HI (icl_memcpy IL) false.
Definition amemmove_libc_spec : Prop := amemcpy_spec_at L ar scfg HI (icl_memmove IL) false.

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
    (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= 17 -> store_ok (hl_segs L) M (Z_to_bv 64 (sp + 16 + d)) m = true) ->
    (forall x, in_shadow_of (sp - 64) 192 x -> byte_at M x 0) ->
    Forall (fun c => cell_is (hl_segs L) M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) (icl_strerror_cells IL) ->
    (forall a, icl_sro_lo IL <= a < icl_sro_hi IL -> M (Z_to_bv 64 a) = None) ->
    Kt [] ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
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
  aic_tls : rt_tls;
  aic_memcpy_libc : amemcpy_libc_spec;
  aic_memmove_libc : amemmove_libc_spec;
  aic_strerror_r22 : astrerror_r22_spec
}.
End IIface.

Record as0_icpt_layout (IL : icpt_layout) : Prop := AICL {
  aicl_strlen : icl_strlen IL = 0x4da8c;
  aicl_scr_strlen : icl_scr_strlen IL = 2304;
  aicl_ro_lo : icl_ro_lo IL = 0x10370; aicl_ro_hi : icl_ro_hi IL = 0x10390;
  aicl_globals : icl_globals IL = [(0x22960, 39); (0x229c0, 13); (0x229e0, 60); (0x22a60, 42); (0x22ac0, 37); (0x22b20, 51); (0x22b80, 13)];
  aicl_poison : icl_poison IL = [(0x22960, 0x22ba0); (0xd9f30, 0xda0f0)];
  aicl_memcpy : icl_memcpy IL = 0x5df40;
  aicl_memmove : icl_memmove IL = 0x5df3c;
  aicl_ctxslot : icl_ctxslot IL = 0x611db0;
  aicl_strerror_r : icl_strerror_r IL = 0x4dae0;
  aicl_scr_strerror : icl_scr_strerror IL = 4320;
  aicl_strerror_cells : icl_strerror_cells IL = [(0x610990, 8, 0x610cd0); (0x610cf8, 8, 0)];
  aicl_sro_lo : icl_sro_lo IL = 0x10000; aicl_sro_hi : icl_sro_hi IL = 0xd7000
}.
