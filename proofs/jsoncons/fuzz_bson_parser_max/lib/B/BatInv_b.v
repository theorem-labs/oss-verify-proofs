(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0Tables
     ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatRzLog_b BatAllocA_b BatInitCache_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatCARSpec_b BatDepotA_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge
     HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Record art_run : Type := ARN {
  rn_ar   : asan_run;        (* [comment removed for export] *)
  rn_t    : Z;               (* [comment removed for export] *)
  rn_ctx  : Z;               (* [comment removed for export] *)
  rn_tp   : Z;               (* [comment removed for export] *)
  rn_key  : Z;               (* [comment removed for export] *)
  rn_tsd  : Z;               (* [comment removed for export] *)
  rn_loff : Z;               (* [comment removed for export] *)
  rn_qs   : Z;               (* [comment removed for export] *)
  rn_kbase : Z;              (* [comment removed for export] *)
  rn_parr : Z;               (* [comment removed for export] *)
  rn_l2   : Z;               (* [comment removed for export] *)
  rn_blk  : Z;               (* [comment removed for export] *)
  rn_dtls : Z                (* [comment removed for export] *)
}.
Definition rn_spb (rn : art_run) : Z := 65536 * rn_qs rn.
Definition rn_ris (rn : art_run) : Z := rn_spb rn + 2 ^ 37.
Definition rn_HI (rn : art_run) : Z := ahl_ceil (rn_ar rn).                       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_RES (rn : art_run) : list (Z * Z) := [(rn_kbase rn, 0x2000011000); (rn_parr rn, 2 ^ 23)].
Definition LENMAX : Z := 2 ^ 27 + 2 ^ 16.
Definition KMAX : Z := 8192.

Definition art_run_ok (rn : art_run) : Prop :=
  art_geo (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_tp rn) (rn_tsd rn) (rn_spb rn) (rn_ris rn) (rn_qs rn)
  /\ ar_space_beg (rn_ar rn) = rn_spb rn
  /\ rn_kbase rn mod 4096 = 0 /\ rn_kbase rn < rn_spb rn <= rn_kbase rn + 65536 /\ rn_kbase rn + 0x2000011000 <= rn_HI rn   (* [comment removed for export] *)
  /\ rn_parr rn mod 4096 = 0 /\ 0x696000 <= rn_parr rn /\ rn_parr rn + 2 ^ 23 <= rn_HI rn /\ app_mem (rn_parr rn) (2 ^ 23)
  /\ 0 <= rn_key rn < 128 /\ 0 <= rn_loff rn /\ 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x696000
  (* [comment removed for export] *)
  /\ 0x661b28 <= rn_tp rn - 88 /\ 0x661b28 <= rn_tsd rn
  /\ rn_l2 rn + 2 ^ 20 <= rn_HI rn /\ rn_blk rn + 2 ^ 23 <= rn_HI rn
  /\ apart (rn_l2 rn) (2 ^ 20) (rn_t rn) 4096 /\ apart (rn_l2 rn) (2 ^ 20) (rn_ctx rn) 4096 /\ apart (rn_l2 rn) (2 ^ 20) (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (rn_l2 rn) (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000)
  /\ apart (rn_blk rn) (2 ^ 23) (rn_t rn) 4096 /\ apart (rn_blk rn) (2 ^ 23) (rn_ctx rn) 4096 /\ apart (rn_blk rn) (2 ^ 23) (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (rn_blk rn) (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000)
  /\ apart (rn_parr rn) (2 ^ 23) (rn_t rn) 4096 /\ apart (rn_parr rn) (2 ^ 23) (rn_ctx rn) 4096 /\ apart (rn_parr rn) (2 ^ 23) (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (rn_parr rn) (2 ^ 23) (rn_l2 rn) (2 ^ 20) /\ apart (rn_parr rn) (2 ^ 23) (rn_blk rn) (2 ^ 23)
  /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_t rn) 4096 /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_ctx rn) 4096 /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_l2 rn) (2 ^ 20) /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_blk rn) (2 ^ 23) /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_parr rn) (2 ^ 23)
  /\ ar_fs (rn_ar rn) + FS_BYTES <= rn_HI rn /\ app_mem (ar_fs (rn_ar rn)) FS_BYTES /\ (ar_fs (rn_ar rn) + FS_BYTES <= 0x10000 \/ 0x696000 <= ar_fs (rn_ar rn)) /\ 4096 <= ar_fs (rn_ar rn)
  (* [comment removed for export] *)
  /\ 0x696000 <= rn_l2 rn /\ 0x696000 <= rn_blk rn
  /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_kbase rn) 0x2000011000
  /\ 4096 <= rn_dtls rn /\ rn_dtls rn + 4096 <= rn_HI rn /\ (rn_dtls rn + 4096 <= 0x10000 \/ 0x696000 <= rn_dtls rn) /\ app_mem (rn_dtls rn) 4096
  /\ apart (rn_dtls rn) 4096 (rn_t rn) 4096 /\ apart (rn_dtls rn) 4096 (rn_ctx rn) 4096 /\ apart (rn_dtls rn) 4096 (rn_kbase rn) 0x2000011000
  /\ apart (rn_dtls rn) 4096 (rn_parr rn) (2 ^ 23) /\ apart (rn_dtls rn) 4096 (rn_l2 rn) (2 ^ 20) /\ apart (rn_dtls rn) 4096 (rn_blk rn) (2 ^ 23)
  /\ apart (rn_dtls rn) 4096 (ar_fs (rn_ar rn)) FS_BYTES
  (* [comment removed for export] *)
  /\ apart (rn_t rn) 4096 (rn_kbase rn) 0x2000011000 /\ apart (rn_ctx rn) 4096 (rn_kbase rn) 0x2000011000
  /\ apart (rn_l2 rn) (2 ^ 20) (rn_kbase rn) 0x2000011000 /\ apart (rn_parr rn) (2 ^ 23) (rn_kbase rn) 0x2000011000
  /\ 0x10007fff8000 <= rn_kbase rn.                                    (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive art_cst : Type :=
| CFree                      (* [comment removed for export] *)
| CAlloc (u n : Z)           (* [comment removed for export] *)
| CQuar (u n : Z)            (* [comment removed for export] *)
| CBatch.                    (* [comment removed for export] *)
Record art_sec : Type := SEC { sc_map : Z; sc_msize : Z; sc_u : Z; sc_n : Z; sc_quar : bool }.
Record art_batch : Type := BATCH { bt_addr : Z; bt_items : list (Z * Z) }.          (* [comment removed for export] *)

Section Inv.
Variable FSG : Type.                                                               (* [comment removed for export] *)

Record art_gs : Type := GS {
  g_log : list aev;                 (* [comment removed for export] *)
  g_inited : bool;                  (* [comment removed for export] *)
  g_cls : Z -> art_cls;             (* [comment removed for export] *)
  g_st : Z -> Z -> art_cst;         (* [comment removed for export] *)
  g_sec : list art_sec;             (* [comment removed for export] *)
  g_sec_committed : bool;           (* [comment removed for export] *)
  g_qt : list art_batch;            (* [comment removed for export] *)
  g_qg : list art_batch;            (* [comment removed for export] *)
  g_depot : nat;                    (* [comment removed for export] *)
  g_ia : bool;                      (* [comment removed for export] *)
  g_fs : FSG
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_rt_tlsgot (M : word -> option byte) : Prop :=
  (forall a, 0x131000 <= a < 0x139000 -> M (Z_to_bv 64 a) = None)
  /\ cellA M 0x673cf8 8 0x673d20 /\ cellA M 0x673d28 8 0x674500.
(* [comment removed for export] *)
Definition art_rt_statics (rn : art_run) (M : word -> option byte) : Prop :=
  art_prim_consts (rn_spb rn) (rn_ris rn) M /\ art_layout M /\ art_tsd M (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn)
  /\ art_alloc_rodata M /\ art_rz_rodata M /\ DRoD M /\ art_rt_tlsgot M
  /\ cellA M 0x140918 1 1 /\ cellA M 0x1c1ea2 1 0 /\ cellA M (1295832 + 3616) 8 (2 ^ 40) /\ cellA M (1295832 + 3624) 2 16 /\ cellA M (1295832 + 3626) 2 2048
  /\ cellA M 0x1d1700 8 0 /\ cellA M 0x1d1708 8 0 /\ cellA M (0x13d438 + 44) 4 4096 /\ cellA M (0x13d438 + 48) 4 0 /\ cellA M (0x13d438 + 52) 4 190 /\ cellA M (0x13d438 + 85) 1 1
  /\ cellA M 0x138120 8 (rn_loff rn) /\ cellA M 0x14093c 4 30 /\ cellA M (0x1d1768 + 34) 1 1
  /\ cellA M (0x13c8b0 + 80) 8 (2 ^ 20) /\ cellA M (0x13c8b0 + 64) 8 (2 ^ 28)
  (* [comment removed for export] *)
  /\ cellA M 0x1374a8 8 0x139508 /\ cellA M 0x139508 8 0x1a476
  (* [comment removed for export] *)
  /\ cellA M 0x140919 1 1 /\ cellA M 0x1d1863 1 1 /\ cellA M 0x1d17f1 1 1 /\ cellA M (0x1d1768 + 84) 1 1 /\ cellA M 0x1cf6d8 4 0
  /\ cellA M 0x13fc40 4 1 /\ cellA M 0x1394c8 8 0x129900
  /\ cellA M 0x137500 8 1                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ cellA M 0x139460 8 0x1107a0 /\ cellA M 0x138028 8 0x140919 /\ cellA M 0x1393c0 8 0x12a8e4 /\ cellA M 0x137510 8 0x1cf6d8 /\ cellA M 0x1382c8 8 8
  (* [comment removed for export] *)
  /\ cellA M 0x1d17bc 1 1 /\ cellA M 0x139318 8 0x130304 /\ cellA M 0x139320 8 0x120d00 /\ cellA M 0x139348 8 0x1273fc /\ cellA M 0x139350 8 0x121118
  (* [comment removed for export] *)
  /\ cellA M 0x1392d0 8 0x1392d0 /\ cellA M 0x13c580 8 1 /\ cellA M 0x13c5d0 1 0 /\ cellA M 0x13d450 4 1 /\ cellA M 0x13d4f0 8 0 /\ cellA M 0x1d1ae0 1 0
  (* [comment removed for export] *)
  /\ cellA M 0x104c0 1 4
  (* [comment removed for export] *)
  /\ cellA M 0x139478 8 0x12a424 /\ cellA M 0x139308 8 0x129804
  (* [comment removed for export] *)
  /\ cellA M 0x13d454 1 0
  (* [comment removed for export] *)
  /\ cellA M 0x139470 8 0x118698
  (* [comment removed for export] *)
  /\ cellA M (0x13d438 + 96) 1 1
  (* [comment removed for export] *)
  /\ cellA M 0x1392f8 8 0x1298d0 /\ cellA M 0x1d1866 1 1 /\ cellA M 0x1d1867 1 1
  (* [comment removed for export] *)
  /\ cellA M 0x10380 8 0xf5f5f5f5f5f5f5f5.
(* [comment removed for export] *)
Definition art_rt_thread (rn : art_run) (M : word -> option byte) : Prop :=
  wrA M (rn_t rn) 4096
  /\ cellA M (rn_t rn) 8 (rn_ctx rn) /\ cellA M (rn_ctx rn + 8) 4 0
  /\ cellA M (rn_t rn + 8) 8 (ar_stack_top (rn_ar rn)) /\ cellA M (rn_t rn + 16) 8 (ar_stack_bottom (rn_ar rn))
  /\ cellA M (rn_t rn + 40) 1 0 /\ cellA M (rn_t rn + 3168) 1 0
  /\ cellA M (rn_tp rn + rn_loff rn) 4 0.
(* [comment removed for export] *)
Definition art_rt_primary (rn : art_run) (G : art_gs) (M : word -> option byte) : Prop :=
  art_pc_hdr (rn_t rn + 208) (g_inited G) M
  /\ (forall c, 1 <= c <= 30 ->
        art_cls_rep (rn_t rn + 208) (rn_spb rn) (rn_ris rn) c (g_cls G c) M /\ art_cls_ok c (g_cls G c)
        /\ (cl_cache (g_cls G c) <> [] -> g_inited G = true) /\ (exists km, cl_mu (g_cls G c) = 262144 * km)
        /\ (0 < cl_au (g_cls G c) -> g_inited G = true))                                              (* [comment removed for export] *)
  /\ wrA M (0x7fff8000 + 8192 * rn_qs rn) (2 ^ 34).
(* [comment removed for export] *)
Definition art_chunk_hdr (M : word -> option byte) (u n st : Z) : Prop :=
  exists b1, 0 <= b1 < 256 /\ b1 mod 4 = 1 /\ cellA M (u - 16) 4 (st + 256 * b1) /\ cellA M (u - 12) 4 n /\ 1 <= n < 2 ^ 28.
(* [comment removed for export] *)
Definition art_lch (M : word -> option byte) (cb u : Z) : Prop :=
  u - 16 <> cb -> cellA M cb 8 0xcc6e96b9cc6e96b9 /\ cellA M (cb + 8) 8 (u - 16).
Definition art_in_batches (bs : list art_batch) (h n : Z) : Prop := exists b, In b bs /\ In (h, n) (bt_items b).
Definition art_rt_chunks (rn : art_run) (G : art_gs) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
  forall c, 1 <= c <= 30 ->
    let cl := g_cls G c in let rb := rn_spb rn + c * 2 ^ 32 in let sz := AsanTab.class_size c in
    (forall x, cl_au cl <= x < cl_mu cl -> x mod 8 = 0 -> byte_at M (S (rb + x)) 0xfa)                 (* [comment removed for export] *)
    /\ (forall w, In w (cl_cache cl ++ cl_free cl) -> g_st G c w = CFree)
    /\ (forall w, ~ art_cptr_ok sz (cl_au cl) w -> g_st G c w = CFree)                                  (* [comment removed for export] *)
    /\ (forall w, art_cptr_ok sz (cl_au cl) w ->
          match g_st G c w with
          | CFree => In w (cl_cache cl ++ cl_free cl) /\ byte_at M (S (rb + 16 * w)) 0xfa
          | CAlloc u n => In (u, n) LB /\ rb + 16 * w + 16 <= u /\ u + n <= rb + 16 * w + sz /\ art_chunk_hdr M u n 2 /\ HAJ.shadow_blkR M u n
                          /\ byte_at M (S (rb + 16 * w)) 0xfa /\ art_lch M (rb + 16 * w) u
          | CQuar u n => rb + 16 * w + 16 <= u /\ u + n <= rb + 16 * w + sz /\ art_chunk_hdr M u n 3 /\ art_in_batches (g_qt G ++ g_qg G) (u - 16) n
                          /\ byte_at M (S (rb + 16 * w)) 0xfa /\ art_lch M (rb + 16 * w) u
          | CBatch => c = 24 /\ exists b, In b (g_qt G ++ g_qg G) /\ bt_addr b = rb + 16 * w
          end).
(* [comment removed for export] *)
Definition art_rt_sec (rn : art_run) (G : art_gs) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
  cellA M (1295832 + 64) 8 4096 /\ cellA M (1295832 + 64 + 8) 8 (rn_parr rn) /\ cellA M (1295832 + 64 + 56) 8 (Z.of_nat (length (g_sec G)))
  /\ cellA M (1295832 + 64 + 48) 8 (if g_sec_committed G then 16384 else 0)
  /\ cellA M (1295832 + 64 + 616) 4 0                                   (* [comment removed for export] *)
  /\ cellA M (1295832 + 64 + 16) 8 (rn_parr rn)                          (* [comment removed for export] *)
  /\ (g_sec G <> [] -> g_sec_committed G = true) /\ (g_sec_committed G = true -> wrA M (rn_parr rn) 131072)
  /\ (forall i s, nth_error (g_sec G) i = Some s ->
        cellA M (rn_parr rn + 8 * Z.of_nat i) 8 (sc_map s)
        /\ In (sc_map s, sc_msize s) (art_live (g_log G)) /\ wrA M (sc_map s) (sc_msize s)
        /\ cellA M (sc_map s) 8 (sc_map s) /\ cellA M (sc_map s + 8) 8 (sc_msize s) /\ cellA M (sc_map s + 24) 8 (Z.of_nat i)
        /\ sc_map s + 4096 <= sc_u s - 16 /\ sc_u s + sc_n s <= sc_map s + sc_msize s
        /\ (if sc_quar s then art_chunk_hdr M (sc_u s) (sc_n s) 3 /\ art_in_batches (g_qt G ++ g_qg G) (sc_u s - 16) (sc_n s)
            else In (sc_u s, sc_n s) LB /\ art_chunk_hdr M (sc_u s) (sc_n s) 2 /\ HAJ.shadow_blkR M (sc_u s) (sc_n s))
        /\ 0x696000 <= sc_map s)                                          (* [comment removed for export] *)
  /\ (forall p, In p (art_live (g_log G)) -> exists s, In s (g_sec G) /\ p = (sc_map s, sc_msize s))
  /\ Z.of_nat (length (g_sec G)) <= 16384.                                                          (* [comment removed for export] *)
(* [comment removed for export] *)
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
  /\ (exists f l, cellA M (0x13c8b0 + 160) 8 (Z.of_nat (length (g_qg G))) /\ cellA M (0x13c8b0 + 168) 8 f /\ cellA M (0x13c8b0 + 176) 8 l
               /\ cellA M (0x13c8b0 + 184) 8 (art_batches_bytes (g_qg G)) /\ art_batch_list M (g_qg G) f l)
  /\ art_batches_bytes (g_qt G) <= 2 ^ 20 /\ art_batches_bytes (g_qg G) <= 2 ^ 28
  /\ cellA M (0x13c8b0 + 152) 4 0                                       (* [comment removed for export] *)
  /\ NoDup (map bt_addr (g_qt G ++ g_qg G))
  (* [comment removed for export] *)
  /\ (forall b, In b (g_qt G ++ g_qg G) -> bt_items b <> [])
  /\ (forall b it, In b (g_qt G ++ g_qg G) -> In it (bt_items b) ->
        (exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls G c)) w /\ g_st G c w = CQuar (fst it + 16) (snd it))
        \/ (exists s, In s (g_sec G) /\ sc_quar s = true /\ sc_u s = fst it + 16 /\ sc_n s = snd it))
  /\ NoDup (map fst (flat_map bt_items (g_qt G ++ g_qg G)))
  /\ (forall b, In b (g_qt G ++ g_qg G) ->                                                            (* [comment removed for export] *)
        exists w, bt_addr b = rn_spb rn + 24 * 2 ^ 32 + 16 * w /\ art_cptr_ok (AsanTab.class_size 24) (cl_au (g_cls G 24)) w /\ g_st G 24 w = CBatch).
(* [comment removed for export] *)
Definition art_rt_depot (rn : art_run) (G : art_gs) (M : word -> option byte) : Prop := DInvD (rn_l2 rn) (rn_blk rn) (g_depot G) M.
Definition art_rt_ia (G : art_gs) (M : word -> option byte) : Prop :=
  cellA M 0x1cf6c8 4 (if g_ia G then 1 else 0)                         (* [comment removed for export] *)
  /\ (g_ia G = true -> forall k, 0 <= k < 2 ^ 15 -> cellA M (0x140e40 + 8 + 8 * k) 8 0)
  /\ (g_ia G = false -> g_qt G = [] /\ g_qg G = []).

(* [comment removed for export] *)
Definition art_rt_blocks (rn : art_run) (G : art_gs) (LB : list (Z * Z)) : Prop :=
  forall b, In b LB ->
    (exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls G c)) w /\ g_st G c w = CAlloc (fst b) (snd b))
    \/ (exists s, In s (g_sec G) /\ sc_quar s = false /\ sc_u s = fst b /\ sc_n s = snd b).

(* [comment removed for export] *)
Definition art_rt_ghost (rn : art_run) (G : art_gs) (M : word -> option byte) : Prop :=
  (forall b it, In b (g_qt G ++ g_qg G) -> In it (bt_items b) -> fst it mod 16 = 0)
  /\ (forall c, 1 <= c <= 30 -> (0 < cl_au (g_cls G c) -> 262144 <= cl_mfa (g_cls G c)) /\ Z.of_nat (length (cl_cache (g_cls G c))) <= art_ic_mc c)
  /\ (forall b, In b (g_qt G ++ g_qg G) -> byte_at M (S (bt_addr b)) 0xfa)
  /\ cellA M (0x13c8b0 + 72) 8 0xe666661.

Definition art_alloc_rep (rn : art_run) (G : art_gs) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
  art_run_ok rn /\ art_rt_statics rn M /\ art_rt_thread rn M /\ art_rt_primary rn G M /\ art_rt_chunks rn G LB M
  /\ art_rt_sec rn G LB M /\ art_rt_quar rn G M /\ art_rt_depot rn G M /\ art_rt_ia G M /\ art_rt_blocks rn G LB
  /\ art_rt_ghost rn G M.                                                                  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_zone_statics (x : Z) : Prop := 0x1394c8 <= x < 0x1394d8 \/ 0x13c580 <= x < 0x1d1980 \/ 0x211b08 <= x < 0x661b28
  \/ 0x139508 <= x < 0x139510                                                         (* [comment removed for export] *)
  \/ 0x1392d0 <= x < 0x1392d8 \/ 0x1392f8 <= x < 0x139358 \/ 0x1393c0 <= x < 0x1393c8 \/ 0x139460 <= x < 0x139480 \/ 0x1d1ae0 <= x < 0x1d1ae1.
  (* [comment removed for export] *)
Definition art_zone_thread (rn : art_run) (x : Z) : Prop := rn_t rn <= x < rn_t rn + 4096 /\ ~ (rn_t rn + 72 <= x < rn_t rn + 80).
Definition art_zone_kspace (rn : art_run) (x : Z) : Prop := rn_kbase rn <= x < rn_kbase rn + 0x2000011000.
Definition art_zone_sec (rn : art_run) (G : art_gs) (x : Z) : Prop :=
  (rn_parr rn <= x < rn_parr rn + 2 ^ 23) \/ (exists p, In p (art_live (g_log G)) /\ fst p <= x < fst p + snd p).
Definition art_zone_depot (rn : art_run) (x : Z) : Prop := dprivD (rn_l2 rn) (rn_blk rn) x.
Definition art_zone_shadow (rn : art_run) (G : art_gs) (x : Z) : Prop :=
  (S (rn_kbase rn) <= x < S (rn_kbase rn + 0x2000011000)) \/ (exists p, In p (art_live (g_log G)) /\ S (fst p) <= x < S (fst p + snd p)).      (* [comment removed for export] *)
Definition art_alloc_zone (rn : art_run) (G : art_gs) (x : Z) : Prop :=
  art_zone_statics x \/ art_zone_thread rn x \/ (rn_ctx rn <= x < rn_ctx rn + 4096) \/ art_zone_kspace rn x \/ art_zone_sec rn G x
  \/ art_zone_depot rn x \/ art_zone_shadow rn G x \/ (0x10000 <= x < 0x139000)
  \/ (rn_tp rn - 88 <= x < rn_tp rn - 80) \/ (rn_tsd rn + 8 * rn_key rn <= x < rn_tsd rn + 8 * rn_key rn + 8)    (* [comment removed for export] *)
  \/ (0x673cf8 <= x < 0x673d00) \/ (0x673d28 <= x < 0x673d30).                                               (* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_fs_zone (rn : art_run) (x : Z) : Prop :=
  (ar_fs (rn_ar rn) <= x < ar_fs (rn_ar rn) + FS_BYTES) \/ (rn_t rn + 72 <= x < rn_t rn + 80)
  \/ (S (ar_fs (rn_ar rn)) <= x < S (ar_fs (rn_ar rn) + FS_BYTES))
  \/ (0x10000 <= x < 0x696000 /\ ~ art_zone_statics x)              (* [comment removed for export] *)
  \/ (S 0x10000 <= x < S 0x696000)                                  (* [comment removed for export] *)
  \/ (rn_dtls rn <= x < rn_dtls rn + 4096).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Variable MAPS0 RESV0 NOACC0 : list (word * word).       (* [comment removed for export] *)
Variable BASE BUDGET : Z.

(* [comment removed for export] *)
Definition art_objs (rn : art_run) : list (Z * Z) :=
  [ (rn_t rn, 4096); (rn_ctx rn, 4096); (rn_kbase rn, 0x2000011000); (rn_parr rn, 2 ^ 23); (rn_l2 rn, 2 ^ 20); (rn_blk rn, 2 ^ 23);
    (ar_fs (rn_ar rn), FS_BYTES);
    (0x10000, 0x41000); (0x51000, 0xe0000); (0x131000, 0x8000); (0x139000, 0x55d000);
    (rn_dtls rn, 4096) ].                                                                     (* [comment removed for export] *)          (* [comment removed for export] *)
Definition art_kn_ok (rn : art_run) : Prop :=
  forall o, In o (art_objs rn) -> exists q, In q (KN0 MAPS0 RESV0) /\ fst q <= fst o /\ fst o + snd o <= snd q.

(* [comment removed for export] *)
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
                          \/ (forall x : word, fst w <= U x < snd w -> page_in_ranges (page_base x) lazy = false))      (* [comment removed for export] *)
  /\ (forall x : word, 2147450880 + 8192 * rn_qs rn <= U x < 2147450880 + 8192 * rn_qs rn + 2 ^ 34 -> page_allowedb A (page_base x) = true)
  /\ (forall x : word, rn_blk rn <= U x < rn_blk rn + 2 ^ 23 -> page_allowedb A (page_base x) = true).

(* [comment removed for export] *)
Definition art_nq (bs : list art_batch) : Z := fold_right (fun b z => 1 + Z.of_nat (length (bt_items b)) + z) 0 bs.
Definition art_nret (G : art_gs) (LB : list (Z * Z)) (cr : credit) : Z := 2 * Z.of_nat (length LB) + art_nq (g_qt G ++ g_qg G) + fst cr.
Definition art_credit_ok (rn : art_run) (G : art_gs) (LB : list (Z * Z)) (cr : credit) : Prop :=
  0 <= fst cr /\ 0 <= snd cr
  /\ art_cost_sum (g_log G) + snd cr + 2 ^ 19 * Z.of_nat (length LB) <= BUDGET
  /\ Z.of_nat (length (art_live (g_log G))) + fst cr <= KMAX
  /\ Z.of_nat (length (g_sec G)) + fst cr <= 16384
  /\ 2 * fst cr + Z.of_nat (length LB) <= Z.of_nat (g_depot G)
  /\ art_nret G LB cr <= 2 ^ 15
  /\ (forall c, 1 <= c <= 30 -> cl_mu (g_cls G c) + 262144 * (fst cr + Z.of_nat (length LB)) <= 3758096384 - 262144
                                /\ Z.of_nat (length (cl_free (g_cls G c))) + Z.of_nat (length (cl_cache (g_cls G c))) + art_nret G LB cr <= 65536).

Definition art_client_ok (rn : art_run) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (M : word -> option byte) : Prop :=
  let ar := rn_ar rn in
  (forall b, In b LB -> 4096 <= fst b /\ (fst b + snd b <= 0x10000 \/ 0x696000 <= fst b) /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= ahl_ceil ar
                      /\ app_mem (fst b) (snd b) /\ defined M (fst b) (snd b) /\ HAJ.shadow_blkR M (fst b) (snd b) /\ shadow_allowed A (fst b) (snd b)
                      /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB) /\ fframes_apart (fst b) (snd b) (FF ++ LK)
                      /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + FS_BYTES <= fst b)
                      /\ (snd b <= 4096 -> 0x10007fff8000 <= fst b))                 (* [comment removed for export] *)
  /\ NoDup (map fst LB)
  /\ shadow_allowed A (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar)              (* [comment removed for export] *)
  /\ shadow_allowed A (ar_fs ar) FS_BYTES                                  (* [comment removed for export] *)
  /\ ahl_ceil ar <= ar_stack_bottom ar + 4096 /\ ar_stack_bottom ar <= ahl_ceil ar + 4096                 (* [comment removed for export] *)
  /\ ar_stack_bottom ar mod 4096 = 0 /\ ar_stack_top ar <= 2 ^ 47 /\ ar_stack_top ar = ar_stack_bottom ar + 8388608
  /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47
  /\ shadow_allowed A 0x10000 (0x696000 - 0x10000)                       (* [comment removed for export] *)
  /\ ar_sptop ar + 16 <= 2 ^ 47                                          (* [comment removed for export] *)
  /\ ar_sptop ar mod 16 = 0.                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition art_eager_ok (LB : list (Z * Z)) (A : list (Z * Z)) (lazy : list (word * word)) : Prop :=
  A_wf A /\ (forall b (x : word), In b LB -> fst b <= U x < fst b + snd b -> page_in_ranges (page_base x) lazy = false).

(* [comment removed for export] *)
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.   (* [comment removed for export] *)

Definition art_ri_inv (rn : art_run) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
           (M : word -> option byte) (V : vml) : Prop :=
  exists G : art_gs,
    art_alloc_rep rn G LB (mrestrict (mkH (snd V) A) M)      (* [comment removed for export] *)
    /\ FSINV rn (g_fs G) FF LK M
    /\ BINV AsanUbsan.M.loaded_segments MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log G) A M (fst V) (snd V)
    /\ art_credit_ok rn G LB cr
    /\ art_client_ok rn LB FF LK A M
    /\ art_kn_ok rn /\ art_lazy_ok rn G A (snd V)                                                     (* [comment removed for export] *)
    /\ art_eager_ok LB A (snd V).                                                                      (* [comment removed for export] *)
Definition art_iface (rn : art_run) : asan_iface := AI (art_ri_inv rn).

(* [comment removed for export] *)
Definition art_alloc_rep_frame_law : Prop :=
  forall rn G LB M M', art_alloc_rep rn G LB M -> mem_grows M M' ->
    (forall x : word, art_alloc_zone rn G (U x) -> ~ in_block LB (U x) -> M' x = M x) ->          (* [comment removed for export] *)
    cellA M' (rn_tp rn + rn_loff rn) 4 0 ->                                                      (* [comment removed for export] *)
    live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log G)) -> art_kn_ok rn ->                       (* [comment removed for export] *)
    art_alloc_rep rn G LB M'.
Definition art_alloc_rep_proj_law : Prop :=
  forall rn G LB M, art_alloc_rep rn G LB M ->
    art_run_ok rn /\ art_layout M /\ art_tsd M (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn)
    /\ cellA M (rn_t rn + 8) 8 (ar_stack_top (rn_ar rn)) /\ cellA M (rn_t rn + 16) 8 (ar_stack_bottom (rn_ar rn)) /\ wrA M (rn_t rn) 4096.
Definition art_fsinv_frame_law : Prop :=
  forall rn gfs FF LK M M', FSINV rn gfs FF LK M -> mem_grows M M' -> (forall x : word, art_fs_zone rn (U x) -> M' x = M x) -> FSINV rn gfs FF LK M'.
(* [comment removed for export] *)
Definition art_gs0 (gfs0 : FSG) (k0 : nat) : art_gs := GS [] false (fun _ => art_cls0) (fun _ _ => CFree) [] false [] [] k0 false gfs0.
Definition art_handoff_target (rn : art_run) (gfs0 : FSG) (k0 : nat) (K0 B0 : Z) (A0 : list (Z * Z)) (M : word -> option byte) (V : vml) : Prop :=
  art_alloc_rep rn (art_gs0 gfs0 k0) [] M /\ FSINV rn gfs0 [] [] M
  /\ BINV AsanUbsan.M.loaded_segments MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET [] A0 M (fst V) (snd V)
  /\ art_credit_ok rn (art_gs0 gfs0 k0) [] (K0, B0) /\ art_client_ok rn [] [] [] A0 M /\ art_kn_ok rn /\ art_lazy_ok rn (art_gs0 gfs0 k0) A0 (snd V)
  /\ art_eager_ok [] A0 (snd V).                                                                        (* [comment removed for export] *)
End Inv.
