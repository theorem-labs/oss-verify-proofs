(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg Hoare AsanAcct HeapIface HeapIfaceA HeapIfaceABx.
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
  aicl_strlen : icl_strlen IL = 0x6336c;
  aicl_scr_strlen : icl_scr_strlen IL = 2304;
  aicl_ro_lo : icl_ro_lo IL = 0x103b0; aicl_ro_hi : icl_ro_hi IL = 0x103d0;
  aicl_globals : icl_globals IL = [(0x231c0, 13); (0x23220, 7); (0x23240, 54); (0x23300, 14); (0x23320, 23); (0x23360, 13); (0x23380, 38); (0x233e0, 43); (0x23440, 66); (0x234c0, 62); (0x23520, 22); (0x23560, 17); (0x235a0, 26); (0x235e0, 19); (0x23620, 19); (0x23660, 23); (0x236a0, 21); (0x236e0, 48); (0x23740, 26); (0x23880, 54); (0x238e0, 9); (0x23900, 4); (0x23920, 39)];
  aicl_poison : icl_poison IL = [(0x231c0, 0x23980); (0x13bfc0, 0x13c580)];
  aicl_memcpy : icl_memcpy IL = 0x77c90;        (* [comment removed for export] *)
  aicl_memmove : icl_memmove IL = 0x77c8c;      (* [comment removed for export] *)
  aicl_ctxslot : icl_ctxslot IL = 0x6951b8;     (* [comment removed for export] *)
  aicl_strerror_r : icl_strerror_r IL = 0x633e4;                                                         (* [comment removed for export] *)
  aicl_scr_strerror : icl_scr_strerror IL = 4320;                                                        (* [comment removed for export] *)
  aicl_strerror_cells : icl_strerror_cells IL = [(0x673cd0, 8, 0x693fc8); (0x693ff0, 8, 0)];             (* [comment removed for export] *)
  aicl_sro_lo : icl_sro_lo IL = 0x10000; aicl_sro_hi : icl_sro_hi IL = 0x139000                            (* [comment removed for export] *)
}.
