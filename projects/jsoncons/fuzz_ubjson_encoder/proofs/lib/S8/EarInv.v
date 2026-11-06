(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem EatLeaf EatAllocG EatPoison EatRzLog EatAllocA EatInitCache ArtRuns EatCls EatCARSpec EatDepotA EatDepot ArtBridge HeapIfaceAEx ShadowRLawsB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Export EarDep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EarDep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Record art_run : Type := ARN {
  rn_ar   : asan_run;
  rn_t    : Z;
  rn_ctx  : Z;
  rn_tp   : Z;
  rn_key  : Z;
  rn_tsd  : Z;
  rn_loff : Z;
  rn_qs   : Z;
  rn_kbase : Z;
  rn_parr : Z;
  rn_l2   : Z;
  rn_blk  : Z;
  rn_dtls : Z                 ;
  rn_keys : list (list Z)
}.

Definition art_rn_k (rn : art_run) (D : list (list Z)) : art_run :=
  ARN (rn_ar rn) (rn_t rn) (rn_ctx rn) (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_loff rn) (rn_qs rn) (rn_kbase rn) (rn_parr rn) (rn_l2 rn) (rn_blk rn) (rn_dtls rn) D.
Definition rn_spb (rn : art_run) : Z := 65536 * rn_qs rn.
Definition rn_ris (rn : art_run) : Z := rn_spb rn + 2 ^ 37.
Definition rn_HI (rn : art_run) : Z := ahl_ceil (rn_ar rn).

Definition art_RES (rn : art_run) : list (Z * Z) := [(rn_kbase rn, 0x2000011000); (rn_parr rn, 2 ^ 23)].
Definition LENMAX : Z := 2 ^ 34 + 2 ^ 16.
Definition KMAX : Z := 4096.

Definition art_run_ok (rn : art_run) : Prop :=
  art_geo (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_tp rn) (rn_tsd rn) (rn_spb rn) (rn_ris rn) (rn_qs rn)
  /\ ar_space_beg (rn_ar rn) = rn_spb rn
  /\ rn_kbase rn mod 4096 = 0 /\ rn_kbase rn < rn_spb rn <= rn_kbase rn + 65536 /\ rn_kbase rn + 0x2000011000 <= rn_HI rn
  /\ rn_parr rn mod 4096 = 0 /\ 0x698000 <= rn_parr rn /\ rn_parr rn + 2 ^ 23 <= rn_HI rn /\ app_mem (rn_parr rn) (2 ^ 23)
  /\ 0 <= rn_key rn < 128 /\ 0 <= rn_loff rn /\ 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x698000

  /\ 0x6638e8 <= rn_tp rn - 88 /\ 0x6638e8 <= rn_tsd rn
  /\ rn_l2 rn + 2 ^ 20 <= rn_HI rn /\ rn_blk rn + 2 ^ 23 <= rn_HI rn
  /\ apart (rn_l2 rn) (2 ^ 20) (rn_t rn) 4096 /\ apart (rn_l2 rn) (2 ^ 20) (rn_ctx rn) 4096 /\ apart (rn_l2 rn) (2 ^ 20) (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (rn_l2 rn) (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000)
  /\ apart (rn_blk rn) (2 ^ 23) (rn_t rn) 4096 /\ apart (rn_blk rn) (2 ^ 23) (rn_ctx rn) 4096 /\ apart (rn_blk rn) (2 ^ 23) (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (rn_blk rn) (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000)
  /\ apart (rn_parr rn) (2 ^ 23) (rn_t rn) 4096 /\ apart (rn_parr rn) (2 ^ 23) (rn_ctx rn) 4096 /\ apart (rn_parr rn) (2 ^ 23) (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (rn_parr rn) (2 ^ 23) (rn_l2 rn) (2 ^ 20) /\ apart (rn_parr rn) (2 ^ 23) (rn_blk rn) (2 ^ 23)
  /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_t rn) 4096 /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_ctx rn) 4096 /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_l2 rn) (2 ^ 20) /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_blk rn) (2 ^ 23) /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_parr rn) (2 ^ 23)
  /\ ar_fs (rn_ar rn) + FS_BYTES <= rn_HI rn /\ app_mem (ar_fs (rn_ar rn)) FS_BYTES /\ (ar_fs (rn_ar rn) + FS_BYTES <= 0x10000 \/ 0x698000 <= ar_fs (rn_ar rn)) /\ 4096 <= ar_fs (rn_ar rn)

  /\ 0x698000 <= rn_l2 rn /\ 0x698000 <= rn_blk rn
  /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_kbase rn) 0x2000011000
  /\ 4096 <= rn_dtls rn /\ rn_dtls rn + 4096 <= rn_HI rn /\ (rn_dtls rn + 4096 <= 0x10000 \/ 0x698000 <= rn_dtls rn) /\ app_mem (rn_dtls rn) 4096
  /\ apart (rn_dtls rn) 4096 (rn_t rn) 4096 /\ apart (rn_dtls rn) 4096 (rn_ctx rn) 4096 /\ apart (rn_dtls rn) 4096 (rn_kbase rn) 0x2000011000
  /\ apart (rn_dtls rn) 4096 (rn_parr rn) (2 ^ 23) /\ apart (rn_dtls rn) 4096 (rn_l2 rn) (2 ^ 20) /\ apart (rn_dtls rn) 4096 (rn_blk rn) (2 ^ 23)
  /\ apart (rn_dtls rn) 4096 (ar_fs (rn_ar rn)) FS_BYTES

  /\ apart (rn_t rn) 4096 (rn_kbase rn) 0x2000011000 /\ apart (rn_ctx rn) 4096 (rn_kbase rn) 0x2000011000
  /\ apart (rn_l2 rn) (2 ^ 20) (rn_kbase rn) 0x2000011000 /\ apart (rn_parr rn) (2 ^ 23) (rn_kbase rn) 0x2000011000
  /\ 0x10007fff8000 <= rn_kbase rn.

Inductive art_cst : Type :=
| CFree
| CAlloc (u n : Z)
| CQuar (u n : Z)
| CBatch.
Record art_sec : Type := SEC { sc_map : Z; sc_msize : Z; sc_u : Z; sc_n : Z; sc_quar : bool }.
Record art_batch : Type := BATCH { bt_addr : Z; bt_items : list (Z * Z) }.

Section Inv.
Variable FSG : Type.

Record art_gs : Type := GS {
  g_log : list aev;
  g_inited : bool;
  g_cls : Z -> art_cls;
  g_st : Z -> Z -> art_cst;
  g_sec : list art_sec;
  g_sec_committed : bool;
  g_qt : list art_batch;
  g_qg : list art_batch;
  g_depot : nat;
  g_ia : bool;
  g_fs : FSG
}.

Definition art_rt_tlsgot (M : word -> option byte) : Prop :=
  (forall a, 0x132000 <= a < 0x13a000 -> M (Z_to_bv 64 a) = None)
  /\ cellA M 0x675a78 8 0x675aa0 /\ cellA M 0x675aa8 8 0x676280.

Definition art_rt_statics (rn : art_run) (M : word -> option byte) : Prop :=
  art_prim_consts (rn_spb rn) (rn_ris rn) M /\ art_layout M /\ art_tsd M (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn)
  /\ art_alloc_rodata M /\ art_rz_rodata M /\ DRoD M /\ art_rt_tlsgot M
  /\ cellA M 0x1426d8 1 1 /\ cellA M 0x1c3c62 1 0 /\ cellA M (1303448 + 3616) 8 (2 ^ 40) /\ cellA M (1303448 + 3624) 2 16 /\ cellA M (1303448 + 3626) 2 2048
  /\ cellA M 0x1d34c0 8 0 /\ cellA M 0x1d34c8 8 0 /\ cellA M (0x13f1f8 + 44) 4 4096 /\ cellA M (0x13f1f8 + 48) 4 0 /\ cellA M (0x13f1f8 + 52) 4 190 /\ cellA M (0x13f1f8 + 85) 1 1
  /\ cellA M 0x139e18 8 (rn_loff rn) /\ cellA M 0x1426fc 4 30 /\ cellA M (0x1d3528 + 34) 1 1
  /\ cellA M (0x13e670 + 80) 8 (2 ^ 20) /\ cellA M (0x13e670 + 64) 8 (2 ^ 28)

  /\ cellA M 0x1391a0 8 0x13b200 /\ cellA M 0x13b200 8 0x1a607

  /\ cellA M 0x1426d9 1 1 /\ cellA M 0x1d3623 1 1 /\ cellA M 0x1d35b1 1 1 /\ cellA M (0x1d3528 + 84) 1 1 /\ cellA M 0x1d1498 4 0
  /\ cellA M 0x141a00 4 1 /\ cellA M 0x13b1c0 8 0x12b488
  /\ cellA M 0x1391f8 8 1

  /\ cellA M 0x13b158 8 0x112324 /\ cellA M 0x139d20 8 0x1426d9 /\ cellA M 0x13b0b8 8 0x12c46c /\ cellA M 0x139208 8 0x1d1498 /\ cellA M 0x139fc0 8 8

  /\ cellA M 0x1d357c 1 1 /\ cellA M 0x13b010 8 0x131e8c /\ cellA M 0x13b018 8 0x122888 /\ cellA M 0x13b040 8 0x128f84 /\ cellA M 0x13b048 8 0x122ca0

  /\ cellA M 0x13afc8 8 0x13afc8 /\ cellA M 0x13e340 8 1 /\ cellA M 0x13e390 1 0 /\ cellA M 0x13f210 4 1 /\ cellA M 0x13f2b0 8 0 /\ cellA M 0x1d38a0 1 0

  /\ cellA M 0x104c8 1 4

  /\ cellA M 0x13b170 8 0x12bfac /\ cellA M 0x13b000 8 0x12b38c

  /\ cellA M 0x13f214 1 0

  /\ cellA M 0x13b168 8 0x11a21c

  /\ cellA M (0x13f1f8 + 96) 1 1

  /\ cellA M 0x13aff0 8 0x12b458 /\ cellA M 0x1d3626 1 1 /\ cellA M 0x1d3627 1 1

  /\ cellA M 0x10390 8 0xf5f5f5f5f5f5f5f5

  /\ cellA M 0x13b050 8 0x128fa0 /\ cellA M 0x13b008 8 0x11dfec.

Definition art_rt_thread (rn : art_run) (M : word -> option byte) : Prop :=
  wrA M (rn_t rn) 4096
  /\ cellA M (rn_t rn) 8 (rn_ctx rn) /\ cellA M (rn_ctx rn + 8) 4 0
  /\ cellA M (rn_t rn + 8) 8 (ar_stack_top (rn_ar rn)) /\ cellA M (rn_t rn + 16) 8 (ar_stack_bottom (rn_ar rn))
  /\ cellA M (rn_t rn + 40) 1 0 /\ cellA M (rn_t rn + 3168) 1 0
  /\ cellA M (rn_tp rn + rn_loff rn) 4 0.

Definition art_rt_primary (rn : art_run) (G : art_gs) (M : word -> option byte) : Prop :=
  art_pc_hdr (rn_t rn + 208) (g_inited G) M
  /\ (forall c, 1 <= c <= 30 ->
        art_cls_rep (rn_t rn + 208) (rn_spb rn) (rn_ris rn) c (g_cls G c) M /\ art_cls_ok c (g_cls G c)
        /\ (cl_cache (g_cls G c) <> [] -> g_inited G = true) /\ (exists km, cl_mu (g_cls G c) = 262144 * km)
        /\ (0 < cl_au (g_cls G c) -> g_inited G = true))
  /\ wrA M (0x7fff8000 + 8192 * rn_qs rn) (2 ^ 34).

Definition art_chunk_hdr (M : word -> option byte) (u n st : Z) : Prop :=
  exists b1, 0 <= b1 < 2 ^ 24 /\ b1 mod 4 = 1 /\ cellA M (u - 16) 4 (st + 256 * b1) /\ cellA M (u - 12) 4 n
             /\ (1 <= n <= 2 ^ 34 /\ b1 / 256 = n / 2 ^ 32 /\ (st = 3 -> n <= 2 ^ 28)).

Definition art_lch (M : word -> option byte) (cb u : Z) : Prop :=
  u - 16 <> cb -> cellA M cb 8 0xcc6e96b9cc6e96b9 /\ cellA M (cb + 8) 8 (u - 16).
Definition art_in_batches (bs : list art_batch) (h n : Z) : Prop := exists b, In b bs /\ In (h, n) (bt_items b).
Definition art_rt_chunks (rn : art_run) (G : art_gs) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
  forall c, 1 <= c <= 30 ->
    let cl := g_cls G c in let rb := rn_spb rn + c * 2 ^ 32 in let sz := AsanTab.class_size c in
    (forall x, cl_au cl <= x < cl_mu cl -> x mod 8 = 0 -> byte_at M (S (rb + x)) 0xfa)
    /\ (forall w, In w (cl_cache cl ++ cl_free cl) -> g_st G c w = CFree)
    /\ (forall w, ~ art_cptr_ok sz (cl_au cl) w -> g_st G c w = CFree)
    /\ (forall w, art_cptr_ok sz (cl_au cl) w ->
          match g_st G c w with
          | CFree => In w (cl_cache cl ++ cl_free cl) /\ byte_at M (S (rb + 16 * w)) 0xfa
          | CAlloc u n => In (u, n) LB /\ rb + 16 * w + 16 <= u /\ u + n <= rb + 16 * w + sz /\ art_chunk_hdr M u n 2 /\ HAJ.shadow_blkR M u n
                          /\ byte_at M (S (rb + 16 * w)) 0xfa /\ art_lch M (rb + 16 * w) u
          | CQuar u n => rb + 16 * w + 16 <= u /\ u + n <= rb + 16 * w + sz /\ art_chunk_hdr M u n 3 /\ art_in_batches (g_qt G ++ g_qg G) (u - 16) n
                          /\ byte_at M (S (rb + 16 * w)) 0xfa /\ art_lch M (rb + 16 * w) u
          | CBatch => c = 24 /\ exists b, In b (g_qt G ++ g_qg G) /\ bt_addr b = rb + 16 * w
          end).

Definition art_rt_sec (rn : art_run) (G : art_gs) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
  cellA M (1303448 + 64) 8 4096 /\ cellA M (1303448 + 64 + 8) 8 (rn_parr rn) /\ cellA M (1303448 + 64 + 56) 8 (Z.of_nat (length (g_sec G)))
  /\ cellA M (1303448 + 64 + 48) 8 (if g_sec_committed G then 16384 else 0)
  /\ cellA M (1303448 + 64 + 616) 4 0
  /\ cellA M (1303448 + 64 + 16) 8 (rn_parr rn)
  /\ (g_sec G <> [] -> g_sec_committed G = true) /\ (g_sec_committed G = true -> wrA M (rn_parr rn) 131072)
  /\ (forall i s, nth_error (g_sec G) i = Some s ->
        cellA M (rn_parr rn + 8 * Z.of_nat i) 8 (sc_map s)
        /\ In (sc_map s, sc_msize s) (art_live (g_log G)) /\ wrA M (sc_map s) (sc_msize s)
        /\ cellA M (sc_map s) 8 (sc_map s) /\ cellA M (sc_map s + 8) 8 (sc_msize s) /\ cellA M (sc_map s + 24) 8 (Z.of_nat i)
        /\ sc_map s + 4096 <= sc_u s - 16 /\ sc_u s + sc_n s <= sc_map s + sc_msize s
        /\ (if sc_quar s then art_chunk_hdr M (sc_u s) (sc_n s) 3 /\ art_in_batches (g_qt G ++ g_qg G) (sc_u s - 16) (sc_n s)
            else In (sc_u s, sc_n s) LB /\ art_chunk_hdr M (sc_u s) (sc_n s) 2 /\ HAJ.shadow_blkR M (sc_u s) (sc_n s))
        /\ 0x698000 <= sc_map s)
  /\ (forall p, In p (art_live (g_log G)) -> exists s, In s (g_sec G) /\ p = (sc_map s, sc_msize s))
  /\ Z.of_nat (length (g_sec G)) <= 16384.

Fixpoint art_batch_list (M : word -> option byte) (bs : list art_batch) (first last : Z) : Prop :=
  match bs with
  | [] => first = 0
  | b :: r =>
      first = bt_addr b /\ (length (bt_items b) <= 1021)%nat
      /\ cellA M (bt_addr b + 16) 8 (Z.of_nat (length (bt_items b)))
      /\ cellA M (bt_addr b + 8) 8 (8192 + fold_right (fun it z => snd it + z) 0 (bt_items b))
      /\ (forall j it, nth_error (bt_items b) j = Some it -> cellA M (bt_addr b + 24 + 8 * Z.of_nat j) 8 (fst it))
      /\ (match r with [] => last = bt_addr b /\ cellA M (bt_addr b) 8 0 | b' :: _ => cellA M (bt_addr b) 8 (bt_addr b') end)
      /\ art_batch_list M r (match r with [] => 0 | b' :: _ => bt_addr b' end) last
  end.
Definition art_batches_bytes (bs : list art_batch) : Z := fold_right (fun b z => 8192 + fold_right (fun it z' => snd it + z') 0 (bt_items b) + z) 0 bs.
Definition art_rt_quar (rn : art_run) (G : art_gs) (M : word -> option byte) : Prop :=
  (exists f l, cellA M (rn_t rn + 80) 8 (Z.of_nat (length (g_qt G))) /\ cellA M (rn_t rn + 88) 8 f /\ cellA M (rn_t rn + 96) 8 l
               /\ cellA M (rn_t rn + 104) 8 (art_batches_bytes (g_qt G)) /\ art_batch_list M (g_qt G) f l)
  /\ (exists f l, cellA M (0x13e670 + 160) 8 (Z.of_nat (length (g_qg G))) /\ cellA M (0x13e670 + 168) 8 f /\ cellA M (0x13e670 + 176) 8 l
               /\ cellA M (0x13e670 + 184) 8 (art_batches_bytes (g_qg G)) /\ art_batch_list M (g_qg G) f l)
  /\ art_batches_bytes (g_qt G) <= 2 ^ 20 /\ art_batches_bytes (g_qg G) <= 2 ^ 28
  /\ cellA M (0x13e670 + 152) 4 0
  /\ NoDup (map bt_addr (g_qt G ++ g_qg G))

  /\ (forall b, In b (g_qt G ++ g_qg G) -> bt_items b <> [])
  /\ (forall b it, In b (g_qt G ++ g_qg G) -> In it (bt_items b) ->
        (exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls G c)) w /\ g_st G c w = CQuar (fst it + 16) (snd it))
        \/ (exists s, In s (g_sec G) /\ sc_quar s = true /\ sc_u s = fst it + 16 /\ sc_n s = snd it))
  /\ NoDup (map fst (flat_map bt_items (g_qt G ++ g_qg G)))
  /\ (forall b, In b (g_qt G ++ g_qg G) ->
        exists w, bt_addr b = rn_spb rn + 24 * 2 ^ 32 + 16 * w /\ art_cptr_ok (AsanTab.class_size 24) (cl_au (g_cls G 24)) w /\ g_st G 24 w = CBatch).

Definition art_rt_depot (rn : art_run) (G : art_gs) (M : word -> option byte) : Prop := DInvK (rn_l2 rn) (rn_blk rn) (g_depot G) (rn_keys rn) M.
Definition art_rt_ia (G : art_gs) (M : word -> option byte) : Prop :=
  cellA M 0x1d1488 4 (if g_ia G then 1 else 0)
  /\ (g_ia G = true -> forall k, 0 <= k < 2 ^ 15 -> cellA M (0x142c00 + 8 + 8 * k) 8 0)
  /\ (g_ia G = false -> g_qt G = [] /\ g_qg G = []).

Definition art_rt_blocks (rn : art_run) (G : art_gs) (LB : list (Z * Z)) : Prop :=
  forall b, In b LB ->
    (exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls G c)) w /\ g_st G c w = CAlloc (fst b) (snd b))
    \/ (exists s, In s (g_sec G) /\ sc_quar s = false /\ sc_u s = fst b /\ sc_n s = snd b).

Definition art_rt_ghost (rn : art_run) (G : art_gs) (M : word -> option byte) : Prop :=
  (forall b it, In b (g_qt G ++ g_qg G) -> In it (bt_items b) -> fst it mod 16 = 0)
  /\ (forall c, 1 <= c <= 30 -> (0 < cl_au (g_cls G c) -> 262144 <= cl_mfa (g_cls G c)) /\ Z.of_nat (length (cl_cache (g_cls G c))) <= art_ic_mc c)
  /\ (forall b, In b (g_qt G ++ g_qg G) -> byte_at M (S (bt_addr b)) 0xfa)
  /\ cellA M (0x13e670 + 72) 8 0xe666661.

Definition art_alloc_rep (rn : art_run) (G : art_gs) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
  art_run_ok rn /\ art_rt_statics rn M /\ art_rt_thread rn M /\ art_rt_primary rn G M /\ art_rt_chunks rn G LB M
  /\ art_rt_sec rn G LB M /\ art_rt_quar rn G M /\ art_rt_depot rn G M /\ art_rt_ia G M /\ art_rt_blocks rn G LB
  /\ art_rt_ghost rn G M.

Definition art_zone_statics (x : Z) : Prop := 0x13b1c0 <= x < 0x13b1d0 \/ 0x13e340 <= x < 0x1d3740 \/ 0x2138c8 <= x < 0x6638e8
  \/ 0x13b200 <= x < 0x13b208
  \/ 0x13afc8 <= x < 0x13afd0 \/ 0x13aff0 <= x < 0x13b058 \/ 0x13b0b8 <= x < 0x13b0c0 \/ 0x13b158 <= x < 0x13b178 \/ 0x1d38a0 <= x < 0x1d38a1.

Definition art_zone_thread (rn : art_run) (x : Z) : Prop := rn_t rn <= x < rn_t rn + 4096 /\ ~ (rn_t rn + 72 <= x < rn_t rn + 80).
Definition art_zone_kspace (rn : art_run) (x : Z) : Prop := rn_kbase rn <= x < rn_kbase rn + 0x2000011000.
Definition art_zone_sec (rn : art_run) (G : art_gs) (x : Z) : Prop :=
  (rn_parr rn <= x < rn_parr rn + 2 ^ 23) \/ (exists p, In p (art_live (g_log G)) /\ fst p <= x < fst p + snd p).
Definition art_zone_depot (rn : art_run) (x : Z) : Prop := dprivD (rn_l2 rn) (rn_blk rn) x.
Definition art_zone_shadow (rn : art_run) (G : art_gs) (x : Z) : Prop :=
  (S (rn_kbase rn) <= x < S (rn_kbase rn + 0x2000011000)) \/ (exists p, In p (art_live (g_log G)) /\ S (fst p) <= x < S (fst p + snd p)).
Definition art_alloc_zone (rn : art_run) (G : art_gs) (x : Z) : Prop :=
  art_zone_statics x \/ art_zone_thread rn x \/ (rn_ctx rn <= x < rn_ctx rn + 4096) \/ art_zone_kspace rn x \/ art_zone_sec rn G x
  \/ art_zone_depot rn x \/ art_zone_shadow rn G x \/ (0x10000 <= x < 0x13a000)
  \/ (rn_tp rn - 88 <= x < rn_tp rn - 80) \/ (rn_tsd rn + 8 * rn_key rn <= x < rn_tsd rn + 8 * rn_key rn + 8)
  \/ (0x675a78 <= x < 0x675a80) \/ (0x675aa8 <= x < 0x675ab0).

Definition art_fs_zone (rn : art_run) (x : Z) : Prop :=
  (ar_fs (rn_ar rn) <= x < ar_fs (rn_ar rn) + FS_BYTES) \/ (rn_t rn + 72 <= x < rn_t rn + 80)
  \/ (S (ar_fs (rn_ar rn)) <= x < S (ar_fs (rn_ar rn) + FS_BYTES))
  \/ (0x10000 <= x < 0x698000 /\ ~ art_zone_statics x)
  \/ (S 0x10000 <= x < S 0x698000)
  \/ (rn_dtls rn <= x < rn_dtls rn + 4096).

Variable MAPS0 RESV0 NOACC0 : list (word * word).
Variable BASE BUDGET : Z.

Definition art_objs (rn : art_run) : list (Z * Z) :=
  [ (rn_t rn, 4096); (rn_ctx rn, 4096); (rn_kbase rn, 0x2000011000); (rn_parr rn, 2 ^ 23); (rn_l2 rn, 2 ^ 20); (rn_blk rn, 2 ^ 23);
    (ar_fs (rn_ar rn), FS_BYTES);
    (0x10000, 0x41000); (0x51000, 0xe1000); (0x132000, 0x8000); (0x13a000, 0x55e000);
    (rn_dtls rn, 4096) ].
Definition art_kn_ok (rn : art_run) : Prop :=
  forall o, In o (art_objs rn) -> exists q, In q (KN0 MAPS0 RESV0) /\ fst q <= fst o /\ fst o + snd o <= snd q.

Definition art_committed (rn : art_run) (G : art_gs) (x : Z) : Prop :=
  (rn_ris rn <= x < rn_ris rn + 4096)
  \/ (exists c, 1 <= c <= 30 /\ (rn_spb rn + c * 2 ^ 32 <= x < rn_spb rn + c * 2 ^ 32 + cl_mu (g_cls G c)
                                 \/ rn_spb rn + c * 2 ^ 32 + 3758096384 <= x < rn_spb rn + c * 2 ^ 32 + 3758096384 + cl_mfa (g_cls G c)))
  \/ (g_sec_committed G = true /\ rn_parr rn <= x < rn_parr rn + 131072).
Definition art_lazy_zone (rn : art_run) (G : art_gs) (x : Z) : Prop :=
  (0x7fff7000 <= x < 0x10007fff8000) \/ (rn_blk rn <= x < rn_blk rn + 2 ^ 23)
  \/ ((rn_kbase rn <= x < rn_kbase rn + 0x2000011000 \/ rn_parr rn <= x < rn_parr rn + 2 ^ 23) /\ ~ art_committed rn G x).
Definition art_lazy_ok (rn : art_run) (G : art_gs) (A : list (Z * Z)) (lazy : list (word * word)) : Prop :=
  (forall w : word, page_in_ranges (page_base w) lazy = true -> art_lazy_zone rn G (U w))
  /\ (forall w, In w A -> (0x7fff7000 <= fst w /\ snd w <= 0x10007fff8000) \/ (rn_blk rn <= fst w /\ snd w <= rn_blk rn + 2 ^ 23)
                          \/ (forall x : word, fst w <= U x < snd w -> page_in_ranges (page_base x) lazy = false))
  /\ (forall x : word, 2147450880 + 8192 * rn_qs rn <= U x < 2147450880 + 8192 * rn_qs rn + 2 ^ 34 -> page_allowedb A (page_base x) = true)
  /\ (forall x : word, rn_blk rn <= U x < rn_blk rn + 2 ^ 23 -> page_allowedb A (page_base x) = true).

Definition art_nq (bs : list art_batch) : Z := fold_right (fun b z => 1 + Z.of_nat (length (bt_items b)) + z) 0 bs.
Definition art_nret (G : art_gs) (LB : list (Z * Z)) (cr : credit) : Z := 2 * Z.of_nat (length LB) + art_nq (g_qt G ++ g_qg G) + fst cr.

Definition KCNT : Z := 8192.
Definition PRIMCAP : Z := 30 * 2 ^ 32.
Definition art_cost_sec (log : list aev) : Z :=
  fold_right (fun ev z => (match ev with AMmapNull len _ => len + len / 8 + 8192 | _ => 0 end) + z) 0 log.
Definition art_primsum (cls : Z -> art_cls) : Z :=
  fold_right (fun c z => cl_mu (cls c) + cl_mfa (cls c) + z) 0 (map Z.of_nat (seq 1 30)).

Definition art_irr (spb : Z) (it : Z * Z) : bool := (snd it <? 64) || (fst it <? spb) || (spb + 7 * 2 ^ 32 <=? fst it).
Definition art_nirr (spb : Z) (l : list (Z * Z)) : Z := Z.of_nat (length (List.filter (art_irr spb) l)).
Definition art_hdrs (LB : list (Z * Z)) : list (Z * Z) := map (fun b => (fst b - 16, snd b)) LB.
Definition art_items (bs : list art_batch) : list (Z * Z) := flat_map bt_items bs.
Definition art_bfull (b : art_batch) : bool := Nat.eqb (length (bt_items b)) 1021.
Definition art_nnonfull (bs : list art_batch) : Z := Z.of_nat (length (List.filter (fun b => negb (art_bfull b)) bs)).
Definition art_qt_ok (bs : list art_batch) : Prop := forall b, In b (removelast bs) -> art_bfull b = true.
Fixpoint art_qg_ok (bs : list art_batch) : Prop :=
  match bs with
  | [] => True
  | b :: r => 2 ^ 20 * art_nnonfull (b :: r) <= art_batches_bytes (b :: r) + 2 ^ 20 /\ art_qg_ok r
  end.
Definition art_credit_ok (rn : art_run) (G : art_gs) (LB : list (Z * Z)) (cr : credit) : Prop :=
  exists irr : Z,
    0 <= fst cr /\ 0 <= snd cr /\ 0 <= irr
    /\ 2 * irr + fst cr + Z.of_nat (length LB) <= KCNT
    /\ art_cost_sec (g_log G) + snd cr + 2 ^ 20 <= BUDGET - PRIMCAP
    /\ art_cost_sum (g_log G) <= art_cost_sec (g_log G) + art_primsum (g_cls G) + (if g_sec_committed G then 131072 else 0)
    /\ Z.of_nat (length (art_live (g_log G))) <= irr
    /\ Z.of_nat (length (g_sec G)) + (KCNT - 2 * irr) <= 16384
    /\ 2 * (fst cr + Z.of_nat (length LB)) <= Z.of_nat (g_depot G)
    /\ art_nirr (rn_spb rn) (art_hdrs LB) + art_nirr (rn_spb rn) (art_items (g_qt G ++ g_qg G)) <= irr
    /\ art_qt_ok (g_qt G) /\ art_qg_ok (g_qg G).

Definition art_client_ok (rn : art_run) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (M : word -> option byte) : Prop :=
  let ar := rn_ar rn in
  (forall b, In b LB -> 4096 <= fst b /\ (fst b + snd b <= 0x10000 \/ 0x698000 <= fst b) /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= ahl_ceil ar
                      /\ app_mem (fst b) (snd b) /\ defined M (fst b) (snd b) /\ HAJ.shadow_blkR M (fst b) (snd b) /\ shadow_allowed A (fst b) (snd b)
                      /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB) /\ fframes_apart (fst b) (snd b) (FF ++ LK)
                      /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b)
                      /\ (snd b <= 4096 -> 0x10007fff8000 <= fst b))
  /\ NoDup (map fst LB)
  /\ shadow_allowed A (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar)
  /\ shadow_allowed A (ar_fs ar) FS_BYTES
  /\ ahl_ceil ar <= ar_stack_bottom ar + 4096 /\ ar_stack_bottom ar <= ahl_ceil ar + 4096
  /\ ar_stack_bottom ar mod 4096 = 0 /\ ar_stack_top ar <= 2 ^ 47 /\ ar_stack_top ar = ar_stack_bottom ar + 8388608
  /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47
  /\ shadow_allowed A 0x10000 (0x698000 - 0x10000)
  /\ ar_sptop ar + 16 <= 2 ^ 47
  /\ ar_sptop ar mod 16 = 0.

Definition art_eager_ok (LB : list (Z * Z)) (A : list (Z * Z)) (lazy : list (word * word)) : Prop :=
  A_wf A /\ (forall b (x : word), In b LB -> fst b <= U x < fst b + snd b -> page_in_ranges (page_base x) lazy = false).

Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.

Definition art_ri_inv (rn : art_run) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
           (M : word -> option byte) (V : vml) : Prop :=
  exists G : art_gs,
    art_alloc_rep rn G LB (mrestrict (mkH (snd V) A) M)
    /\ FSINV rn (g_fs G) FF LK M
    /\ BINV Asan.M.loaded_segments MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log G) A M (fst V) (snd V)
    /\ art_credit_ok rn G LB cr
    /\ art_client_ok rn LB FF LK A M
    /\ art_kn_ok rn /\ art_lazy_ok rn G A (snd V)
    /\ art_eager_ok LB A (snd V).
Definition art_iface (rn : art_run) : asan_iface := AI (art_ri_inv rn).

Lemma art_dk_up : forall l2 blk k k' D D' (M : word -> option byte), DInvK l2 blk k D M -> DInvK l2 blk k' D' M -> DInvK l2 blk k D' M.
Proof. intros l2 blk k k' D D' M [H1 _] [_ H2]. split; [exact H1 | exact H2]. Qed.
Lemma art_rep_keys : forall rn D G LB M, art_alloc_rep rn G LB M -> DInvK (rn_l2 rn) (rn_blk rn) (g_depot G) D M -> art_alloc_rep (art_rn_k rn D) G LB M.
Proof.
  intros rn D G LB M REP DK. unfold art_alloc_rep in *.
  destruct REP as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|]. split; [exact C7|]. split; [exact DK|]. exact C9.
Qed.
Lemma art_ri_inv_keys : (forall rn D g FF LK M, FSINV rn g FF LK M -> FSINV (art_rn_k rn D) g FF LK M) ->
  forall rn D LB FF LK cr A M V,
  art_ri_inv rn LB FF LK cr A M V ->
  (forall k, DInvK (rn_l2 rn) (rn_blk rn) k (rn_keys rn) (mrestrict (mkH (snd V) A) M) -> DInvK (rn_l2 rn) (rn_blk rn) k D (mrestrict (mkH (snd V) A) M)) ->
  art_ri_inv (art_rn_k rn D) LB FF LK cr A M V.
Proof.
  intros FSK rn D LB FF LK cr A M V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) UP.
  exists G. split; [apply art_rep_keys; [exact REP|]|].
  { apply UP. destruct REP as (_ & _ & _ & _ & _ & _ & _ & DEP & _). exact DEP. }
  split; [apply FSK; exact FS|]. split; [exact BV|]. split; [exact CRED|]. split; [exact CLI|]. split; [exact KN|]. split; [exact LZ|exact EG].
Qed.

Definition art_alloc_rep_frame_law : Prop :=
  forall rn G LB M M', art_alloc_rep rn G LB M -> mem_grows M M' ->
    (forall x : word, art_alloc_zone rn G (U x) -> ~ in_block LB (U x) -> M' x = M x) ->
    cellA M' (rn_tp rn + rn_loff rn) 4 0 ->
    live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log G)) -> art_kn_ok rn ->
    art_alloc_rep rn G LB M'.
Definition art_alloc_rep_proj_law : Prop :=
  forall rn G LB M, art_alloc_rep rn G LB M ->
    art_run_ok rn /\ art_layout M /\ art_tsd M (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn)
    /\ cellA M (rn_t rn + 8) 8 (ar_stack_top (rn_ar rn)) /\ cellA M (rn_t rn + 16) 8 (ar_stack_bottom (rn_ar rn)) /\ wrA M (rn_t rn) 4096.
Definition art_fsinv_frame_law : Prop :=
  forall rn gfs FF LK M M', FSINV rn gfs FF LK M -> mem_grows M M' -> (forall x : word, art_fs_zone rn (U x) -> M' x = M x) -> FSINV rn gfs FF LK M'.

Definition art_gs0 (gfs0 : FSG) (k0 : nat) : art_gs := GS [] false (fun _ => art_cls0) (fun _ _ => CFree) [] false [] [] k0 false gfs0.
Definition art_handoff_target (rn : art_run) (gfs0 : FSG) (k0 : nat) (K0 B0 : Z) (A0 : list (Z * Z)) (M : word -> option byte) (V : vml) : Prop :=
  art_alloc_rep rn (art_gs0 gfs0 k0) [] M /\ FSINV rn gfs0 [] [] M
  /\ BINV Asan.M.loaded_segments MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET [] A0 M (fst V) (snd V)
  /\ art_credit_ok rn (art_gs0 gfs0 k0) [] (K0, B0) /\ art_client_ok rn [] [] [] A0 M /\ art_kn_ok rn /\ art_lazy_ok rn (art_gs0 gfs0 k0) A0 (snd V)
  /\ art_eager_ok [] A0 (snd V).
End Inv.
