(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx As0Tables
     ArtMem EbtLeaf EbtAllocG EbtPoison EbtRzLog EbtAllocA EbtInitCache ArtRuns EbtCls EbtCARSpec EbtDepotA EbtDepot ArtBridge
     HeapIfaceAEx ShadowRLawsB.      (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Export EbrDep.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import EbrDep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_EbrInv () := "C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC35stdpp4base6ElemOfC46Stdlib5Lists4List:fold_rightI35stdpp4base<list_elem_of00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrDep5DInvKC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EbtDepot5DInvDC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrDep6dp_hasC13~~~K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4prod00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv=art_alloc_repC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv5rn_l2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv6rn_blkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv7g_depotC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv:art_run_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv8art_rn_kC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv>art_rt_staticsC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv=art_rt_threadC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv>art_rt_primaryC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv=art_rt_chunksC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv:art_rt_secC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv<art_rt_ghostC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv;art_rt_quarC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv<art_rt_depotC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv=art_rt_blocksC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv9art_rt_iaC13~~~i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv7art_run00C13~~~i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv6art_gs00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv:art_ri_invC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv4g_fsC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv5rn_HIC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv5g_logC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv=art_credit_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv=art_client_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv<art_eager_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv9art_kn_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv;art_lazy_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv7rn_keysC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv<art_rep_keysC13~~~K47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes3sndC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct3mkHC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct9mrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9ArtBridge4BINVC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images9AsanUbsan1M?loaded_segmentsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA3vmlC13~~~I47Corelib4Init5Logic2ex00".   (* [comment removed for export] *)
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
  rn_dtls : Z                (* [comment removed for export] *);
  rn_keys : list (list Z)   (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition art_rn_k (rn : art_run) (D : list (list Z)) : art_run :=
  ARN (rn_ar rn) (rn_t rn) (rn_ctx rn) (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_loff rn) (rn_qs rn) (rn_kbase rn) (rn_parr rn) (rn_l2 rn) (rn_blk rn) (rn_dtls rn) D.
Definition rn_spb (rn : art_run) : Z := 65536 * rn_qs rn.
Definition rn_ris (rn : art_run) : Z := rn_spb rn + 2 ^ 37.
Definition rn_HI (rn : art_run) : Z := ahl_ceil (rn_ar rn).                       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_RES (rn : art_run) : list (Z * Z) := [(rn_kbase rn, 0x2000011000); (rn_parr rn, 2 ^ 23)].
Definition LENMAX : Z := 2 ^ 31 + 2 ^ 16.                  (* [comment removed for export] *)
Definition KMAX : Z := 8192.

Definition art_run_ok (rn : art_run) : Prop :=
  art_geo (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_tp rn) (rn_tsd rn) (rn_spb rn) (rn_ris rn) (rn_qs rn)
  /\ ar_space_beg (rn_ar rn) = rn_spb rn
  /\ rn_kbase rn mod 4096 = 0 /\ rn_kbase rn < rn_spb rn <= rn_kbase rn + 65536 /\ rn_kbase rn + 0x2000011000 <= rn_HI rn   (* [comment removed for export] *)
  /\ rn_parr rn mod 4096 = 0 /\ 0x69c000 <= rn_parr rn /\ rn_parr rn + 2 ^ 23 <= rn_HI rn /\ app_mem (rn_parr rn) (2 ^ 23)
  /\ 0 <= rn_key rn < 128 /\ 0 <= rn_loff rn /\ 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x69c000
  (* [comment removed for export] *)
  /\ 0x667fe8 <= rn_tp rn - 88 /\ 0x667fe8 <= rn_tsd rn
  /\ rn_l2 rn + 2 ^ 20 <= rn_HI rn /\ rn_blk rn + 2 ^ 23 <= rn_HI rn
  /\ apart (rn_l2 rn) (2 ^ 20) (rn_t rn) 4096 /\ apart (rn_l2 rn) (2 ^ 20) (rn_ctx rn) 4096 /\ apart (rn_l2 rn) (2 ^ 20) (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (rn_l2 rn) (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000)
  /\ apart (rn_blk rn) (2 ^ 23) (rn_t rn) 4096 /\ apart (rn_blk rn) (2 ^ 23) (rn_ctx rn) 4096 /\ apart (rn_blk rn) (2 ^ 23) (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (rn_blk rn) (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000)
  /\ apart (rn_parr rn) (2 ^ 23) (rn_t rn) 4096 /\ apart (rn_parr rn) (2 ^ 23) (rn_ctx rn) 4096 /\ apart (rn_parr rn) (2 ^ 23) (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (rn_parr rn) (2 ^ 23) (rn_l2 rn) (2 ^ 20) /\ apart (rn_parr rn) (2 ^ 23) (rn_blk rn) (2 ^ 23)
  /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_t rn) 4096 /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_ctx rn) 4096 /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_spb rn) (2 ^ 37 + 4096)
  /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_l2 rn) (2 ^ 20) /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_blk rn) (2 ^ 23) /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_parr rn) (2 ^ 23)
  /\ ar_fs (rn_ar rn) + FS_BYTES <= rn_HI rn /\ app_mem (ar_fs (rn_ar rn)) FS_BYTES /\ (ar_fs (rn_ar rn) + FS_BYTES <= 0x10000 \/ 0x69c000 <= ar_fs (rn_ar rn)) /\ 4096 <= ar_fs (rn_ar rn)
  (* [comment removed for export] *)
  /\ 0x69c000 <= rn_l2 rn /\ 0x69c000 <= rn_blk rn
  /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_kbase rn) 0x2000011000
  /\ 4096 <= rn_dtls rn /\ rn_dtls rn + 4096 <= rn_HI rn /\ (rn_dtls rn + 4096 <= 0x10000 \/ 0x69c000 <= rn_dtls rn) /\ app_mem (rn_dtls rn) 4096
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
  (forall a, 0x137000 <= a < 0x13f000 -> M (Z_to_bv 64 a) = None)
  /\ cellA M 0x67a178 8 0x67a1a0 /\ cellA M 0x67a1a8 8 0x67a980.
(* [comment removed for export] *)
Definition art_rt_statics (rn : art_run) (M : word -> option byte) : Prop :=
  art_prim_consts (rn_spb rn) (rn_ris rn) M /\ art_layout M /\ art_tsd M (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn)
  /\ art_alloc_rodata M /\ art_rz_rodata M /\ DRoD M /\ art_rt_tlsgot M
  /\ cellA M 0x146dd8 1 1 /\ cellA M 0x1c8362 1 0 /\ cellA M (1321624 + 3616) 8 (2 ^ 40) /\ cellA M (1321624 + 3624) 2 16 /\ cellA M (1321624 + 3626) 2 2048
  /\ cellA M 0x1d7bc0 8 0 /\ cellA M 0x1d7bc8 8 0 /\ cellA M (0x1438f8 + 44) 4 4096 /\ cellA M (0x1438f8 + 48) 4 0 /\ cellA M (0x1438f8 + 52) 4 190 /\ cellA M (0x1438f8 + 85) 1 1
  /\ cellA M 0x13e528 8 (rn_loff rn) /\ cellA M 0x146dfc 4 30 /\ cellA M (0x1d7c28 + 34) 1 1
  /\ cellA M (0x142d70 + 80) 8 (2 ^ 20) /\ cellA M (0x142d70 + 64) 8 (2 ^ 28)
  (* [comment removed for export] *)
  /\ cellA M 0x13d8b0 8 0x13f910 /\ cellA M 0x13f910 8 0x1a76e
  (* [comment removed for export] *)
  /\ cellA M 0x146dd9 1 1 /\ cellA M 0x1d7d23 1 1 /\ cellA M 0x1d7cb1 1 1 /\ cellA M (0x1d7c28 + 84) 1 1 /\ cellA M 0x1d5b98 4 0
  /\ cellA M 0x146100 4 1 /\ cellA M 0x13f8d0 8 0x12fc30
  /\ cellA M 0x13d908 8 1                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ cellA M 0x13f868 8 0x116acc /\ cellA M 0x13e430 8 0x146dd9 /\ cellA M 0x13f7c8 8 0x130c14 /\ cellA M 0x13d918 8 0x1d5b98 /\ cellA M 0x13e6d0 8 8
  (* [comment removed for export] *)
  /\ cellA M 0x1d7c7c 1 1 /\ cellA M 0x13f720 8 0x136634 /\ cellA M 0x13f728 8 0x127030 /\ cellA M 0x13f750 8 0x12d72c /\ cellA M 0x13f758 8 0x127448
  (* [comment removed for export] *)
  /\ cellA M 0x13f6d8 8 0x13f6d8 /\ cellA M 0x142a40 8 1 /\ cellA M 0x142a90 1 0 /\ cellA M 0x143910 4 1 /\ cellA M 0x1439b0 8 0 /\ cellA M 0x1d7fa0 1 0
  (* [comment removed for export] *)
  /\ cellA M 0x104d0 1 4
  (* [comment removed for export] *)
  /\ cellA M 0x13f880 8 0x130754 /\ cellA M 0x13f710 8 0x12fb34
  (* [comment removed for export] *)
  /\ cellA M 0x143914 1 0
  (* [comment removed for export] *)
  /\ cellA M 0x13f878 8 0x11e9c4
  (* [comment removed for export] *)
  /\ cellA M (0x1438f8 + 96) 1 1
  (* [comment removed for export] *)
  /\ cellA M 0x13f700 8 0x12fc00 /\ cellA M 0x1d7d26 1 1 /\ cellA M 0x1d7d27 1 1
  (* [comment removed for export] *)
  /\ cellA M 0x10398 8 0xf5f5f5f5f5f5f5f5
  (* [comment removed for export] *)
  /\ cellA M 0x13f760 8 0x12d748 /\ cellA M 0x13f718 8 0x122794.
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
  exists b1, 0 <= b1 < 256 /\ b1 mod 4 = 1 /\ cellA M (u - 16) 4 (st + 256 * b1) /\ cellA M (u - 12) 4 n /\ 1 <= n <= 2 ^ 31.          (* [comment removed for export] *)
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
  cellA M (1321624 + 64) 8 4096 /\ cellA M (1321624 + 64 + 8) 8 (rn_parr rn) /\ cellA M (1321624 + 64 + 56) 8 (Z.of_nat (length (g_sec G)))
  /\ cellA M (1321624 + 64 + 48) 8 (if g_sec_committed G then 16384 else 0)
  /\ cellA M (1321624 + 64 + 616) 4 0                                   (* [comment removed for export] *)
  /\ cellA M (1321624 + 64 + 16) 8 (rn_parr rn)                          (* [comment removed for export] *)
  /\ (g_sec G <> [] -> g_sec_committed G = true) /\ (g_sec_committed G = true -> wrA M (rn_parr rn) 131072)
  /\ (forall i s, nth_error (g_sec G) i = Some s ->
        cellA M (rn_parr rn + 8 * Z.of_nat i) 8 (sc_map s)
        /\ In (sc_map s, sc_msize s) (art_live (g_log G)) /\ wrA M (sc_map s) (sc_msize s)
        /\ cellA M (sc_map s) 8 (sc_map s) /\ cellA M (sc_map s + 8) 8 (sc_msize s) /\ cellA M (sc_map s + 24) 8 (Z.of_nat i)
        /\ sc_map s + 4096 <= sc_u s - 16 /\ sc_u s + sc_n s <= sc_map s + sc_msize s
        /\ (if sc_quar s then art_chunk_hdr M (sc_u s) (sc_n s) 3 /\ art_in_batches (g_qt G ++ g_qg G) (sc_u s - 16) (sc_n s)
            else In (sc_u s, sc_n s) LB /\ art_chunk_hdr M (sc_u s) (sc_n s) 2 /\ HAJ.shadow_blkR M (sc_u s) (sc_n s))
        /\ 0x69c000 <= sc_map s)                                          (* [comment removed for export] *)
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
  /\ (exists f l, cellA M (0x142d70 + 160) 8 (Z.of_nat (length (g_qg G))) /\ cellA M (0x142d70 + 168) 8 f /\ cellA M (0x142d70 + 176) 8 l
               /\ cellA M (0x142d70 + 184) 8 (art_batches_bytes (g_qg G)) /\ art_batch_list M (g_qg G) f l)
  /\ art_batches_bytes (g_qt G) <= 2 ^ 20 /\ art_batches_bytes (g_qg G) <= 2 ^ 28
  /\ cellA M (0x142d70 + 152) 4 0                                       (* [comment removed for export] *)
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
Definition art_rt_depot (rn : art_run) (G : art_gs) (M : word -> option byte) : Prop := DInvK (rn_l2 rn) (rn_blk rn) (g_depot G) (rn_keys rn) M.   (* [comment removed for export] *)
Definition art_rt_ia (G : art_gs) (M : word -> option byte) : Prop :=
  cellA M 0x1d5b88 4 (if g_ia G then 1 else 0)                         (* [comment removed for export] *)
  /\ (g_ia G = true -> forall k, 0 <= k < 2 ^ 15 -> cellA M (0x147300 + 8 + 8 * k) 8 0)
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
  /\ cellA M (0x142d70 + 72) 8 0xe666661.

Definition art_alloc_rep (rn : art_run) (G : art_gs) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
  art_run_ok rn /\ art_rt_statics rn M /\ art_rt_thread rn M /\ art_rt_primary rn G M /\ art_rt_chunks rn G LB M
  /\ art_rt_sec rn G LB M /\ art_rt_quar rn G M /\ art_rt_depot rn G M /\ art_rt_ia G M /\ art_rt_blocks rn G LB
  /\ art_rt_ghost rn G M.                                                                  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_zone_statics (x : Z) : Prop := 0x13f8d0 <= x < 0x13f8e0 \/ 0x142a40 <= x < 0x1d7e40 \/ 0x217fc8 <= x < 0x667fe8
  \/ 0x13f910 <= x < 0x13f918                                                         (* [comment removed for export] *)
  \/ 0x13f6d8 <= x < 0x13f6e0 \/ 0x13f700 <= x < 0x13f768 \/ 0x13f7c8 <= x < 0x13f7d0 \/ 0x13f868 <= x < 0x13f888 \/ 0x1d7fa0 <= x < 0x1d7fa1.
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
  \/ art_zone_depot rn x \/ art_zone_shadow rn G x \/ (0x10000 <= x < 0x13f000)
  \/ (rn_tp rn - 88 <= x < rn_tp rn - 80) \/ (rn_tsd rn + 8 * rn_key rn <= x < rn_tsd rn + 8 * rn_key rn + 8)    (* [comment removed for export] *)
  \/ (0x67a178 <= x < 0x67a180) \/ (0x67a1a8 <= x < 0x67a1b0).                                               (* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_fs_zone (rn : art_run) (x : Z) : Prop :=
  (ar_fs (rn_ar rn) <= x < ar_fs (rn_ar rn) + FS_BYTES) \/ (rn_t rn + 72 <= x < rn_t rn + 80)
  \/ (S (ar_fs (rn_ar rn)) <= x < S (ar_fs (rn_ar rn) + FS_BYTES))
  \/ (0x10000 <= x < 0x69c000 /\ ~ art_zone_statics x)              (* [comment removed for export] *)
  \/ (S 0x10000 <= x < S 0x69c000)                                  (* [comment removed for export] *)
  \/ (rn_dtls rn <= x < rn_dtls rn + 4096).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Variable MAPS0 RESV0 NOACC0 : list (word * word).       (* [comment removed for export] *)
Variable BASE BUDGET : Z.

(* [comment removed for export] *)
Definition art_objs (rn : art_run) : list (Z * Z) :=
  [ (rn_t rn, 4096); (rn_ctx rn, 4096); (rn_kbase rn, 0x2000011000); (rn_parr rn, 2 ^ 23); (rn_l2 rn, 2 ^ 20); (rn_blk rn, 2 ^ 23);
    (ar_fs (rn_ar rn), FS_BYTES);
    (0x10000, 0x42000); (0x52000, 0xe5000); (0x137000, 0x8000); (0x13f000, 0x55d000);
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
(* [comment removed for export] *)
Definition KCNT : Z := 8192.
Definition PRIMCAP : Z := 30 * 2 ^ 32.
Definition art_cost_sec (log : list aev) : Z :=
  fold_right (fun ev z => (match ev with AMmapNull len _ => len + len / 8 + 8192 | _ => 0 end) + z) 0 log.
Definition art_primsum (cls : Z -> art_cls) : Z :=
  fold_right (fun c z => cl_mu (cls c) + cl_mfa (cls c) + z) 0 (map Z.of_nat (seq 1 30)).
(* [comment removed for export] *)
Definition art_irr (spb : Z) (it : Z * Z) : bool := (snd it <? 64) || (fst it <? spb) || (spb + 7 * 2 ^ 32 <=? fst it).
Definition art_nirr (spb : Z) (l : list (Z * Z)) : Z := Z.of_nat (length (List.filter (art_irr spb) l)).
Definition art_hdrs (LB : list (Z * Z)) : list (Z * Z) := map (fun b => (fst b - 16, snd b)) LB.     (* [comment removed for export] *)
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
    /\ Z.of_nat (length (art_live (g_log G))) + (KCNT - 2 * irr) <= KMAX
    /\ Z.of_nat (length (g_sec G)) + (KCNT - 2 * irr) <= 16384
    /\ 2 * (fst cr + Z.of_nat (length LB)) <= Z.of_nat (g_depot G)
    /\ art_nirr (rn_spb rn) (art_hdrs LB) + art_nirr (rn_spb rn) (art_items (g_qt G ++ g_qg G)) <= irr
    /\ art_qt_ok (g_qt G) /\ art_qg_ok (g_qg G).

Definition art_client_ok (rn : art_run) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (M : word -> option byte) : Prop :=
  let ar := rn_ar rn in
  (forall b, In b LB -> 4096 <= fst b /\ (fst b + snd b <= 0x10000 \/ 0x69c000 <= fst b) /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= ahl_ceil ar
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
  /\ shadow_allowed A 0x10000 (0x69c000 - 0x10000)                       (* [comment removed for export] *)
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
Lemma art_dk_up : forall l2 blk k k' D D' (M : word -> option byte), DInvK l2 blk k D M -> DInvK l2 blk k' D' M -> DInvK l2 blk k D' M.
Proof.
ltac2:(KReplay.run1 (kr_t_EbrInv ()) ["Inv"] "h02wsh11Hh21Dh32D'h42H1h52H2h61Mh72_Hh83_H0h93blkh:1kh;2k'h<2l2p;1p;5p;4p;3p-1R0g0000R1p4p710p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p7210p8P0p10023p4p710R0p8p1002Op4p70p1003[p4p710p8p10048p4p710R4P3p8P4P2p8P4P0p8g004Mj17Tg004mj10Tg005Rj16Tg0060j15Tg006Sj19Tg0075j54Tg008<j41TP1j32Tg009Ej33Tg00:Mj48Tg00:hR1g00;FR0%71R4#7R2g00;e#0#0#0R3#0#0#0#6#5%63#5#9[f6R3f5R5f4R6f2R7f0R8D4g00<JR9f7R:P3P5f1R;C1A2486f3R<f9R=;3;[^04f8R>P:P5P<P7D4P=P>P:P6P<D4[P8P=P>P:P<C1A248:f<R<=33;[^04f;R6f:R7P>P3P5D4P9P<P6P=P3C1A248>f>R==3>;[^04f=R9P<P6P>P:D4P8P=P9P6P>C1A2486fA=36;[^04f@f?P=P7C1A248<fB=3<;[^04P3P8C8W5W8P;P8O2n2001000000120000000W1W7W4P;P8O2n2001000000120000000W1W6X32W2X;0W:X91W<o"). Qed.
Lemma art_rep_keys : forall rn D G LB M, art_alloc_rep rn G LB M -> DInvK (rn_l2 rn) (rn_blk rn) (g_depot G) D M -> art_alloc_rep (art_rn_k rn D) G LB M.
Proof.
ltac2:(KReplay.run1 (kr_t_EbrInv ()) ["Inv"] "h01Hh12C1h22C2h32C3h42C4h52C5h62C6h72C7h82C8h92C9h:1Dh;2DKh<1Gh=2LBh>1Mh?3REPh@2rnp;1p;2p;4p;5p;3g004Mj1ETg00<ej2RTg004mj1:Tg005Rj1GTg0060j1LTg006Sj1QTg00=Ej4JTg00>Tj1PTg00?[j1OTg00@cj1NTg0075j5MTg00Alj1CTg00C8j26Tg00DBj2?Tg00ERj2>Tg00Faj3<Tg00H1j4;Tg00I@j4BTg00JLj39Tg00KZj3ATg00Lgj3=Tg00<JR0j20Tg00:Mj48Tg00N5j3ITg00ODj2FTf5R1f4R2f3R33If2R4f1R5f0R639'0p=1A=1231F45/06'0p=2f7R7f6R8P1P2CBAA345/06'0p=3A<781P2P3P4P5C;/06'0p=D1?231>45/06'0p=KP2P3P4P5C;/06p=41>12A<345/06'0p=5%C31?45/06'0p=71F12AI345/06'0p=@AA812A=345/06'0p=Hg00POg00:hR9#E#Eg00QZ1R99#Eg00;e#:#:#:R9#:#:#:#G#L%G9#L#Q[P2P4P5P6CJ%P1%O1%N3P2P5DMP0%C8P8P4P8P4P8P2P4P8P2P3P4P8P2P3P4P8P2P4P8P2P4P2P4P8P2P3P8P2P4E1E2G3GDDK1678R9P9P3P9P3P9P1P3P9P1P2P3P9P1P2P3P9P1P3P9P1P3P1P3P9P1P2P9P1P3E1E2G3D4E5C7P5f8R9#Cf9R:P1P:P1P:P7P1P:P7P8P1P:P7P8P1P:P7P1P:P7P1P7P1P:P7P8P:P7P1E1E2G3GDDKP0f:R;/?8P;P8P;P9P8P;P9P7P8P;P9P7P8P;P9P8P;P9P8P9P8P;P9P7P;P9P8E1E2G3D4E5f;R</6;R=P=P7P=P7P=P:P7P=P:P9P7P=P:P9P7P=P:P7P=P:P7P:P7P=P:P9P=P:P7E1E2G3D4E5C7P6f<R7/?9f=R9P:P9P<P:P9P<P;P:P9P<P;P:P9P<P:P9P<P:P<P:P9P<P;P9P<P:E1E2G3D4E5P0f>R=/>;P=P7P;P=P7P<P;P=P7P<P;P=P7P;P=P7P;P7P;P=P7P<P=P7P;E1E2G3GDf?R;/6=R>P>P<P>P<P>P9P<P>P9P7P<P>P9P7P<P>P9P<P>P9P<P9P<P>P9P7P>P9P<E1E2G3D4E5C7P6f@R</>7fAR7P;P9P7P;P=P9P7P;P=P9P7P;P9P7P;P9P;P9P7P;P=P7P;P9E1E2G3GDP0fBR>?<<=P>P<P;P=P>P<P;P=P>P<P=P>P<P=P<P=P>P<P;P>P<P=E1E2G3D4fCR=/6>R?P?P;P?P;P?P7P;P?P7P<P;P?P7P<P;P?P7P;P?P7P;P7P;P?P7P<P?P7P;E1E2G3D4E5C7P6fDR;?<><fER<P=P>P7P<P=P>P7P<P=P7P<P=P7P=P7P<P=P>P<P=P7E1E2G3D4P0fFR?P;P=P>C;P?P;P=P>P?P;P>P?P;P>P;P>P?P;P=P?P;P>E1E2G3fGR>/6?R@P@P=P@P=P@P<P=P@P<P;P=P@P<P;P=P@P<P=P@P<P=P<P=P@P<P;P@P<P=E1E2G3D4E5C7P6fHR=P?P<P;C;fIR;P>P?P<P;P>P<P;P>P<P>P<P;P>P?P;P>P<E1E2G3P0fJR@P=P>P?CBP@P=P?P@P=P?P=P?P@P=P>A9@=?E@FHfKR?/6@RAPAP>PAP>PAP;P>PAP;P=P>PAP;P=P>PAP;P>PAP;P>P;P>PAP;P=PAP;P>E1E2G3D4E5C7P6fLR>P@P;P=CBfMR=P?P;P=P?P;P?P;P=P?P@A9=?;E@FHP0fNRA?A>@PAP>P@P>P@PAP>P?PAP>P@E1E2fOR@/6ARBPBP?PBP?PBP=P?PBP=P>P?PBP=P>P?PBP=P?PBP=P?P=P?PBP=P>PBP=P?E1E2G3D4E5C7P6fPR??AA>fQR>P@P=P@P=P>P@PAP>P@P=E1E2P0fRR0?=?AP?PAP0P?P@A90?AE@fSRA/60RBPBP@PBP@PBP>P@PBP>P?P@PBP>P?P@PBP>P@PBP>P@P>P@PBP>P?PBP>P@E1E2G3D4E5C7P6fTR@?=0?PAP>fURBPAP0A9BA>E@fV/6BRB#C1?B0R>1>B0RCA<B@0RDPBP@PAP0C;REPBP@PAP0CBRFAAB@0RGA=B@0RHP@P0PBP@PAA9B@0E@RB'0R@'0R0'0RA'0RI'0RJ'0RK'0P=P>PKP;PCPJP<PDPIP7PEPAP9PFP0P:PGP@P1PHPBP?P6C8C8C8C8C8C8C8C8W9W8P5P6O2n2001000000121000000W0W7P5P6O2n2001000000121000000W0W6P5P6O2n2001000000121000000W0W5P5P6O2n2001000000121000000W0W4P5P6O2n2001000000121000000W0W3P5P6O2n2001000000121000000W0W2P5P6O2n2001000000121000000W0W1P5P6O2n20010000001210000001681P2P3P4CJeW;W?W>W=W<W:W@o"). Qed.
Lemma art_ri_inv_keys : (forall rn D g FF LK M, FSINV rn g FF LK M -> FSINV (art_rn_k rn D) g FF LK M) ->
  forall rn D LB FF LK cr A M V,
  art_ri_inv rn LB FF LK cr A M V ->
  (forall k, DInvK (rn_l2 rn) (rn_blk rn) k (rn_keys rn) (mrestrict (mkH (snd V) A) M) -> DInvK (rn_l2 rn) (rn_blk rn) k D (mrestrict (mkH (snd V) A) M)) ->
  art_ri_inv (art_rn_k rn D) LB FF LK cr A M V.
Proof.
ltac2:(KReplay.run1 (kr_t_EbrInv ()) ["Inv"] "p'0h01Hh11kh21Gh31Dh42FFh52LKh61Mh72rnh81Ah92BVh:3CLIh;4CREDh<3DEPh=2EGh>2FSh?3FSKh@2KNhA2LBhB2LZhC3REPhD2UPhE1VhF2_HhG3_H0hH3_H1hI3_H2hJ3_H3hK3_H4hL3_H5hM3_H6hN2crhO1gi001xp;1p;2p;8p;4p;6p;3p;5p;7p;<g004Mj1RTg004mj1LTg005Rj1cTg0060j1aTg006Sj1nTg00C8j29Tg00<ej2eTg00Rdj8?Tg00=Ej4ITg00T0j1HTg00U6j1:Tg00V=j1BTg00WDj4>Tg00XSj6TTg00Ybj3KTg00[0j1PTg00\;j4OTg00>Tj1NTg00?[j1MTg0075j5JTg00<JR0j20Tg00@cj1@Tg00Alj1`Tg00DBj2STg00ERj2GTg00Faj3ATg00H1j4FTg00]Hj1_Tg00I@j4^Tg00JLj3QTg00KZj3UTg00Lgj3ZTg00^Qj7lTg00:Mj4ETg00__j4kTg00`9j3]Tg00`Vj2YTg00a]j2XTg000cj3jTg00bjl<iTg00N5j3dTg00ODj2fTg00d3R1f1R2f0R33]p=2f2R4/Y2/X3p=CAj123p==g00djP3P2P4f3R5f4R6f5R7f6R8f7R9f8R:f9R;f:R<M<ip=;P8P7P6P5COAK423'0p=4P9P8P7P6P5P4ET%P2/03'0p=81023,04p=3%N9%M8P7%_6A]154/Y2/X3DJp=7%N6%M5P4P2P3DJp=hP6P5P4P2C>/03p=WA]154/Y2/X3p=1%N6%M5P4%_2P3DJp=V%N8%M7P6P51Y42/X3DJp=D%P7P6P5P4P2CO/03'0p=bAd765AQ423'0p=6AZ7651f42/03'0p=5P9P8P7P6C^AU542/03'0p=<P6P5%@4P2P3DJp=mP6P5P4P2CF/03p=\1f76Ad542/03'0p=[AU876AZ542/03'0p=gg00POR1g00:hR=#R#RR>p,3FSGg002O#RR?g00;e#L#L#LR@#L#L#L#c#aRA%c@#a#n[R@p,5FSINVRBP7P5P4P2P3O5PB1987P6P5P4P2O5[]6^5?]4]O]3]71e==#RR=g00f<g00gGP:P8P7P6P5P4P2P3G?g00hPg00QZRCP<P3P:1eAA#RRA/24RD?C65CIPBP<%H3REP9P8P5O5p,5MAPS0RFp,5RESV0RGp,6NOACC0RH%:<p,4BASERIp,6BUDGETRJ%B3RKP6P51=A4PDM;;P<P3P:P7C>P<P:P9P8P6P5P<P<P3P6PDP:P6PDF4G83333X2Cg00;FRDf;RLPLP3PLPAP5P7P6G7f<RMPMP2PL12A6RN?C87RODh[]119L<P;P:P9P8P7P6P5G?[P3PMP3P<POCIPBPMPEP;P:P7O5PFPGPH%:MPIPJPKP8P71=A6PNM;;PMP3P<P9C>PMP<P;P:P8P7PMPMP3P8PNP<P8PNF4G83333P0f=RNP2PL12A7RO?C98CIPBPN%H2P<P;P8O5PFPGPH%:NPIPJ%B2P9P81=A7POM;;PNP2PLP:PNPLP<P;P9P8PNPNP2P9POPLP9POF4G8DW33f?ROPOP3POPAP9P;P:C1RPDVf@RQPQP2PO12A:RRP<P;FD[^1Df>RS,9OPNPMPLP<P;P:P9G?[P3POP5PNPPCIPBPQ%H6PNPMP;O5PFPGPH%:QPIPJ%B6P<P;1=A:PRM;;PQP6PSPLPQPSPNPMP<P;PQPQP6P<PRPSP<PRF4G8DW33P0PBfARR%H7PSPNP<O5PFPGPH%:RPIPJ%B7PLP<1=A;12A;R6M;;PRP7POPMC>PRPOPSPNPLP<PRPRP7PLP6POPLP6F4G833fCR6P6P3P6PAPLPNPMG7fDR7P7P2P612AMRPPSPNFD[^1DfBR5,96PRPQPOPSPNPMPLG?[P3PBP6%H9PQPOPMO5PFPGPH%:7PIPJ%B:PSPN1=AMPPM;;P7P:P5POC>P7P5PRPQPSPNP7P7P:PSPPP5PSPPF4G833P0PFPGPHfERP#:PIPJ%B;POPS1=AN12ANR:M;;PPP;P6PQPPP6P5PRPOPSPPPPP;POP:P6POP:F4G8DWfGR:P:P3P:12AOR;?CRQDVfHR9P9P2P:12AQRTP5PRFD[^1DfFRU,9:PPP7P6P5PRPQPOG?[P3PFPGPH%::PIPJ%BLPRPQ1=AOP;M;;P9PMPUP6P9PUPPP7P5PRP9P9PMP5PTPUP5PTF4G8DWP0fIRTPNP:P7C>PTP:PUPPP6P5PTPTPNP612ARRNP:P6PNF4G8fKRNPNP3PNPAP6PPP7G7fLRMPMP2PN12A7R;PUPPFD[^1DfJRL,9NPTP9P:PUPPP7P6G?[P3PNPOPTPUC>PMPLPTP9PUPPPMPMPQPUP;PLPUP;F4G8P0fMR;PNPLPTP:PUETP;P;PRP:12APRRAKN:REbfORRPRP3PRPAP:PTP9G7fPRQPQP2PR12A9ROPLPTFD[^1DfNR6,9RP;PMPNPLPTP9P:G?[P3PRP;PMPNPTP9ETPQPQP7PLPOAK6LOEbP0fQRO#PPOPPPN12ATRPPRPNPPF4fSRPPPP3PPPAPNP;PMG7fTR7P7P2PP12AMR:P6P;FD[^1DfRRV,9PPOPQPRP6P;PMPNG?[P3%PPP7P9P6P:PVP6P:F4P0fUR:PTPR12A;R;COAKPR;fWR;P;P3P;12ARRT?COQDVfXR9P9P2P;12AQRMPVPOFD[^1DfVRW,9;P:P7PPPVPOPQPRG?[P3P;PNPOPTCOAKWVMfZRMPMP3PM12AVRT?C7PRNDVf[RQ#NRX%MQRYP2PM12APRZ?C:7R[DJ[^1DPC19QMRDP3fYR\P[CIPBPDPEP9P;P7O5PFPGPH%:DPIPJPKP:P71=APPZM;;PDP3P\PWC>PDP\P9P;P:P7PDPDP3P:PZP\P:PZF4G83333X2CP619M\RZP6P9PNCIPBPZ%H6RBP;PWPPO5RDPFPGPH%:ZPIPJ%B6P7PP1=AVPTM;;RJPZP6P9P:C>RIPZP9P;PWP7PPETRH%PZRGPZP6P7PTCORZAK97TRT'0R7'0RF'0RK'0RE'0R]'0PMP\P6P9PNPLP3%@6P0%`M1SMN1GMNAAM6NPMP6P9PNCFPMP6P9PNPMP6PNPMP6PNP6PNPMP6P9PMP6PNE6E5G<3333PXPYPR%_QP[DmPLf\RL#`f]R[PAP:P;PWC1RR'S1G[RAA[ORP[POPQPRCFP[POPQPRP[POPRP[POPRPOPRP[POPQP[POPRE6E5G<3333P0f^RRPAPWP9P;C1RO'S1GROAARVOPRPVPLPOPRPVPLPOPRPVPOPRPVPOPVPOPRPVPLPRPVPOE6E5G<D\33f_ROPO%@PPOPAP;P\P9G7P3f`RVPAP9PMP\C1'SfaR9PAP\PQPMC1RY'GAA9:YP9P:POPYP9P:POPYP9P:PYP9P:PYP:PYP9P:POP9P:PYE6E5G<D\33P0fbRYPAPMPLPQC1R:'GAAYW:PYPWPVP:CFPYPWPVP:PYPWP:PYPWP:PWP:PYPWPVPYPWP:E6E5G<33fcR:P:%@;P:PAPQP[PLG7P3fdRXPAPLPRP[C1'GfeRNPAP[POPRC1R67A\PNP\P:P6CFPNP\P:P6PNP\P6PNP\P6P\P6PNP\P:PNP\P6E6E5G<33P0ffR6PAPRPVPOC1R^7AMP6PMPXP^P6PMPXP^P6PMP^P6PMP^PMP^P6PMPXP6PMP^E6E5G<D\fgR^P^%@QP^PAPOP9PVG7P3fhR_PAPVPYP9C17ALfiRLP[P^PAP9P:PYC1R`PLP[P^P`PLP[P`PLP[P`P[P`PLP[P^PLP[P`E6E5G<D\P0fjR`PRP_PAPYPXP:C1R[CFP`PRP_P[P`PRP[P`PRP[PRP[P`PRP_P`PRP[E6E5G<fkR[P[%@OP[PAP:PNPXG7P3flROPVP`PAPXP6PNC1CFfmRVP9P[PAPNP^P6C1RRPVP9PRPVP9PRP9PRPVP9P[PVP9PRE6E5G<P0fnRRPYPOPAP6P_P^C1R9C^PRPYP9PRPYP9PYP9PRPYPOAQRY9E[FgfoR9P9%@:P9PAP^PLP_G7P3fpR:PXPRPAP_P`PLC1C^fqRXPNPAPLP[P`C1RYPXPNPYPNPYPXPNP9AQXNYE[FgP0frRYPAP`POP[C1RN7U6PYP6PNP6PNPYP6P:PYP6PNE6E5fsRNPN%@^PNPAP[PVPOG7P3ftR^PAPOPRPVC17U_fuR_PLPAPVP9PRC1R6PLP6P_PLPNP_PLP6E6E5P0fvR0PAPRP:P9C1RR7Z`P`PRP0P`P^AQ0`RE[fwRRPR%@[PRPAP9PXP:G7P3fxPAP:PYPXC17ZOPVPAPXPNPYC1RYfyRNPVPRAQNVYE[P2WMW<P2P3O2n2001000000120000000W0WLP2P3O2n2001000000121000000W0WKP2P3O2n2001000000121000000W0WJP2P3O2n2001000000121000000W0WIP2P3O2n2011000000121000000W0WHP2P3O2n2011000000121000000W0WGP2P3O2n2011000000121000000W0WFP2P3O2n2011000000121000000O2FlPDP]PQPMP\PBP;PWPPPUO7PJPEP5PIPKPSPHPFP<PGP7P8PZPTP4P2CECECECECECECECkWDW=WBP2P3O2n2001000000121000000W0W@P2P3O2n2001000000121000000W0W:P2P3O2n2001000000121000000W0W;P2P3O2n2001000000121000000W0W9P2P3O2n2001000000121000000W0W>P2P3O2n2001000000121000000W0WCP2P3O2n2001000000121000000W0X2CP2P3O2n2001000000121100000W0WEX6@X8=WNX5?X4?WAX3>X71W?o"). Qed.

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
