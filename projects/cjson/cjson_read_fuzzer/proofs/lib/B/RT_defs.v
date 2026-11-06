(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AIMG_LO  : Z := 0x10000.
Definition AIMG_HI  : Z := 0x5ff000.
Definition ADATA_LO : Z := 0xa1000.

(* [comment removed for export] *)
Definition A_ALLOC        : Z := 0xa6358.            (* [comment removed for export] *)
Definition A_SPACEBEG     : Z := A_ALLOC + 32.        (* [comment removed for export] *)
Definition A_RIS          : Z := A_ALLOC + 48.        (* [comment removed for export] *)
Definition A_RTOI_MS      : Z := A_ALLOC + 40.        (* [comment removed for export] *)
Definition A_PREMAPPED    : Z := A_ALLOC + 56.        (* [comment removed for export] *)
Definition A_SECONDARY    : Z := A_ALLOC + 64.        (* [comment removed for export] *)
Definition A_GSTATS       : Z := A_ALLOC + 688.       (* [comment removed for export] *)
Definition A_QUAR         : Z := A_ALLOC + 728.       (* [comment removed for export] *)
Definition A_FALLBACK_MU  : Z := A_ALLOC + 984.
Definition A_FALLBACK_AC  : Z := A_ALLOC + 992.
Definition A_FALLBACK_QC  : Z := A_ALLOC + 3584.
Definition A_MAXUSERSZ    : Z := A_ALLOC + 3616.      (* [comment removed for export] *)
Definition A_MINRZ        : Z := A_ALLOC + 3624.      (* [comment removed for export] *)
Definition A_MAXRZ        : Z := A_ALLOC + 3626.      (* [comment removed for export] *)
Definition A_ADMISMATCH   : Z := A_ALLOC + 3628.      (* [comment removed for export] *)

Definition QUAR_MAX_SIZE   : Z := 0x10000000.         (* [comment removed for export] *)
Definition QUAR_MIN_SIZE   : Z := 0xe666661.          (* [comment removed for export] *)
Definition QUAR_MAX_CACHE  : Z := 0x100000.           (* [comment removed for export] *)
Definition QBATCH_SIZE     : Z := 8192.               (* [comment removed for export] *)
Definition QBATCH_CAP      : Z := 1021.               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_ASAN_INITED      : Z := 0xaa698.  (* [comment removed for export] *)
Definition A_REPLACE_INTRIN   : Z := 0xaa699.  (* [comment removed for export] *)
Definition A_INIT_RUNNING     : Z := 0xaa69a.  (* [comment removed for export] *)
Definition A_KHIGHMEMEND      : Z := 0xaa6a0.  (* [comment removed for export] *)
Definition A_KMIDMEMBEG       : Z := 0xaa6a8.  (* [comment removed for export] *)
Definition A_KMIDMEMEND       : Z := 0xaa6b0.  (* [comment removed for export] *)
Definition A_MCS              : Z := 0xaa6bc.  (* [comment removed for export] *)
Definition A_UNKNOWN_STATS    : Z := 0xaa6e8.
Definition A_CAN_POISON       : Z := 0xa921c.  (* [comment removed for export] *)
Definition A_TSD_KEY_INITED   : Z := 0xa9220.  (* [comment removed for export] *)
Definition A_TSD_KEY          : Z := 0xa9224.  (* [comment removed for export] *)
Definition A_SHADOW_OFF_CELL  : Z := 0xa99b8.  (* [comment removed for export] *)
Definition A_UAR_OPTION       : Z := 0xa99c0.  (* [comment removed for export] *)
Definition A_ALLOC_OOM        : Z := 0x12bc20.  (* [comment removed for export] *)
Definition A_MAY_RETURN_NULL  : Z := 0x12bc21.  (* [comment removed for export] *)
Definition A_RSS_EXCEEDED     : Z := 0x12bc22.  (* [comment removed for export] *)
Definition A_PAGESIZE_CACHED  : Z := 0x139460.  (* [comment removed for export] *)
Definition A_LIBC_PAGESIZE   : Z := 0x5fcc30.  (* [comment removed for export] *)
Definition A_IA_INITED        : Z := 0x139448.  (* [comment removed for export] *)
Definition A_IA_MU            : Z := 0x139449.
Definition A_IA_INSTANCE      : Z := 0xaabc0.  (* [comment removed for export] *)
Definition A_IA_MAP1          : Z := 0xaabc8.  (* [comment removed for export] *)
Definition A_DYING            : Z := 0x13b4dc.  (* [comment removed for export] *)
Definition A_MFHOOKS          : Z := 0x13b480.  (* [comment removed for export] *)
Definition A_AFLAGS           : Z := 0xa71b8.  (* [comment removed for export] *)
Definition A_MU_GLOBALS       : Z := 0xa7270.  (* [comment removed for export] *)
Definition A_GLOBALS_REGD     : Z := 0xa6300.  (* [comment removed for export] *)
Definition A_TPCG_INITED      : Z := 0x13b860.  (* [comment removed for export] *)
Definition A_GLOBREC_LO       : Z := 0xa6020.  (* [comment removed for export] *)
Definition A_GLOBREC_HI       : Z := 0xa62e0.  (* [comment removed for export] *)
Definition A_CFLAGS           : Z := 0x13b4e8.  (* [comment removed for export] *)
Definition A_REAL_MEMSET_SLOT : Z := 0xa3588.  (* [comment removed for export] *)
Definition A_REAL_MEMCPY_SLOT : Z := 0xa3580.  (* [comment removed for export] *)
Definition A_MUSL_MEMSET      : Z := 0x9ad74.
Definition A_MUSL_MEMCPY      : Z := 0x9a970.
Definition A_MUSL_STRLEN      : Z := 0x9afc0.

(* [comment removed for export] *)
Definition A_STACKSTORE   : Z := 0x17b888.  (* [comment removed for export] *)
Definition A_DEPOT        : Z := 0x18b898.  (* [comment removed for export] *)
Definition A_DEPOT_NIDS   : Z := 0x58b898.  (* [comment removed for export] *)
Definition A_DEPOT_MU     : Z := 0x58b8a0.
Definition A_DEPOT_MAP1   : Z := 0x58b8a8.  (* [comment removed for export] *)
Definition DEPOT_TAB_LOG  : Z := 20.
Definition DEPOT_NODE_SZ  : Z := 16.
Definition DEPOT_L2_NODES : Z := 65536.     (* [comment removed for export] *)
Definition SSTORE_BLOCK_FRAMES : Z := 2^20. (* [comment removed for export] *)
Definition SSTORE_NBLOCKS : Z := 4096.
Definition DEPOT_TMAX     : Z := 2^32 - 2^20. (* [comment removed for export] *)
Definition TRACE_MAX_LEN  : Z := 30.          (* [comment removed for export] *)
Definition DEPOT_KMAX     : Z := 2^20.     (* [comment removed for export] *)
Definition DEPOT_NNB_MAX  : Z := 18.       (* [comment removed for export] *)
Definition DEPOT_NSB_MAX  : Z := 34.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ATP        : Z := 0x5dc970.     (* [comment removed for export] *)
Definition AERRNO     : Z := ATP - 164.    (* [comment removed for export] *)
Definition A_TSD_PTR  : Z := ATP - 88.     (* [comment removed for export] *)
Definition A_TSD_MAIN : Z := 0x5fdd18.     (* [comment removed for export] *)
Definition A_DTV_PTR  : Z := ATP - 8.      (* [comment removed for export] *)
Definition A_LSAN_DISABLE : Z := ATP + 0x10. (* [comment removed for export] *)
Definition A_FAKESTACK_TLSDESC : Z := 0xa23e0.  (* [comment removed for export] *)
Definition A_DTLS_TLSOFF_SLOT : Z := 0xa23f0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_CTX := 0.  Definition T_STACK_TOP := 8.  Definition T_STACK_BOTTOM := 16.
Definition T_SWITCHING := 40.  Definition T_TLS_BEGIN := 48.  Definition T_TLS_END := 56.
Definition T_FAKESTACK := 72.  Definition T_QCACHE := 80.  Definition T_ACACHE := 208.
Definition T_STATS := 2800.  Definition T_UNWINDING := 3168.
Definition CTX_TID := 8.  Definition CTX_THREAD := 152.
(* [comment removed for export] *)
Definition roundup (x a : Z) : Z := (x + a - 1) / a * a.
Definition ASTACK_TOP (sp0 : Z) : Z := roundup (sp0 - 0xa0) 4096.
Definition ASTACK_BOTTOM (sp0 : Z) : Z := ASTACK_TOP sp0 - 0x800000.

(* [comment removed for export] *)
Definition GOT_SHADOW_OFF : Z := 0xa1700.  Definition GOT_AFLAGS : Z := 0xa16f8.  Definition GOT_CFLAGS : Z := 0xa16f0.
Definition GOT_PAGESIZE : Z := 0xa16e0.    Definition GOT_KMIDBEG : Z := 0xa1708. Definition GOT_KMIDEND : Z := 0xa1710.
Definition GOT_KHIGHEND : Z := 0xa1718.    Definition GOT_REAL_MEMSET : Z := 0xa1720. Definition GOT_REAL_MEMCPY : Z := 0xa1728.
Definition GOT_SEALED : Z := 0xa1740.      (* [comment removed for export] *)
Definition GOT_DYING : Z := 0xa1748.       (* [comment removed for export] *)
Definition GOT_UAR : Z := 0xa1758.         (* [comment removed for export] *)
Definition GOT_SILENT : Z := 0xa22c8.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AHOOKS   : Z := 0xa5cc0.  (* [comment removed for export] *)
Definition AGERROR0 : Z := 0x5dc040.  (* [comment removed for export] *)
Definition AGERROR1 : Z := 0x5dc048.  (* [comment removed for export] *)
Definition AEMPTY   : Z := 0x5dc020.  (* [comment removed for export] *)
Definition ALCONV   : Z := 0xa1598.  (* [comment removed for export] *)
Definition ADOTSTR  : Z := 0x142c3.   (* [comment removed for export] *)
Definition ASSP     : Z := 0x5fc9b0.  (* [comment removed for export] *)
Definition AGOT_SSP : Z := 0xa2388.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AGLOB_STRS : list (Z * Z) :=
  [(0x211e0,5); (0x21200,6); (0x21220,5); (0x21240,3); (0x21260,7); (0x21280,4); (0x212a0,7); (0x212c0,3); (0x212e0,6)].

(* [comment removed for export] *)
Definition AMALLOC  : Z := 0x544c0.  Definition AFREE : Z := 0x544bc.  Definition AREALLOC : Z := 0x544c4.
Definition ASTKMALLOC1 : Z := 0x3d4b0.  Definition ASTKMALLOC2 : Z := 0x3d640.
Definition AASANMEMCPY : Z := 0x5316c.  Definition AASANMEMSET : Z := 0x53608.
Definition AMEMCPY_T : Z := 0x53168.  Definition AMEMSET_T : Z := 0x53164.  Definition AMEMMOVE_T : Z := 0.  (* [comment removed for export] *)
Definition ASTRLEN_T : Z := 0x424fc. Definition ASTRNCMP_T : Z := 0x42508. Definition ASPRINTF_T : Z := 0x42544.
Definition ASSCANF_T : Z := 0x42530. Definition AVPRINTF_T : Z := 0x42534. Definition ASTRTOD : Z := 0x9a5b0.
Definition ALOCALECONV : Z := 0x8e0ec.
(* [comment removed for export] *)
Definition PC0_MALLOC : Z := 0x54760.  Definition PC0_FREE : Z := 0x54600.  Definition PC0_REALLOC : Z := 0x549fc.
(* [comment removed for export] *)
Definition ASPINS : list Z := [0x34f48; 0x3656c; 0x55b4c; 0x618bc; 0x6198c; 0x6fde0; 0x6ff70; 0x79cc8].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KNUMCLASSES : Z := 32.
Definition KMAXSIZE : Z := 0x10000.
Definition KREGIONSIZE : Z := 2^32.
Definition KFREEARRAY_OFF : Z := 0xe0000000.   (* [comment removed for export] *)
Definition KFREEARRAY_SIZE : Z := 2^29.
Definition KUSERMAP : Z := 2^18.               (* [comment removed for export] *)
Definition KSPACESIZE : Z := 2^37.

Fixpoint log2_floor_pos (p : positive) : Z :=
  match p with xH => 0 | xO q => 1 + log2_floor_pos q | xI q => 1 + log2_floor_pos q end.
Definition log2_floor (n : Z) : Z := match n with Zpos p => log2_floor_pos p | _ => 0 end.

(* [comment removed for export] *)
Definition csize (c : Z) : Z :=
  if c =? 31 then 64
  else if c <=? 16 then 32 * c
  else let t := Z.shiftl 512 ((c - 16) / 2) in t + (if Z.odd (c - 16) then t / 2 else 0).

(* [comment removed for export] *)
Definition classid (s : Z) : Z :=
  if s <=? 512 then (s + 31) / 32
  else let l := log2_floor s in
       let hbit := (Z.shiftr s (l - 1)) mod 2 in
       let lbits := s mod (2 ^ (l - 1)) in
       16 + 2 * (l - 9) + hbit + (if 0 <? lbits then 1 else 0).

(* [comment removed for export] *)
Definition clampz (x lo hi : Z) : Z := Z.max lo (Z.min hi x).
Definition cmaxcount (c : Z) : Z := 2 * clampz (1024 / csize c) 1 8.

(* [comment removed for export] *)
Definition rz_log (n : Z) : Z :=
  if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
  else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz_size (n : Z) : Z := Z.shiftl 16 (rz_log n).
(* [comment removed for export] *)
Definition usz (n : Z) : Z := Z.max n 1.
Definition rounded8 (n : Z) : Z := roundup (Z.max n 8) 8.
Definition needed0 (n : Z) : Z := rounded8 n + rz_size n.
Definition is_primary (n : Z) : bool := needed0 n <=? KMAXSIZE.
Definition needed (n : Z) : Z := if is_primary n then needed0 n else needed0 n + rz_size n.
(* [comment removed for export] *)
Definition pclass (n : Z) : Z := classid (needed0 n).
Definition pslot (n : Z) : Z := csize (pclass n).
(* [comment removed for export] *)
Definition smapsize (n : Z) : Z := roundup (needed n) 4096 + 4096.
(* [comment removed for export] *)
Definition asz (n : Z) : Z := if is_primary n then pslot n else smapsize n.

Definition region_beg (spacebeg c : Z) : Z := spacebeg + c * KREGIONSIZE.
Definition free_array (spacebeg c : Z) : Z := region_beg spacebeg c + KFREEARRAY_OFF.
Definition compact_of (spacebeg c p : Z) : Z := (p - region_beg spacebeg c) / 16.
Definition chunk_of_compact (spacebeg c k : Z) : Z := region_beg spacebeg c + 16 * k.

(* [comment removed for export] *)
Definition CHUNK_INVALID : Z := 0.  Definition CHUNK_ALLOCATED : Z := 2.  Definition CHUNK_QUARANTINE : Z := 3.
Definition HDR_BYTE1_MALLOC : Z := 0x11.   (* [comment removed for export] *)
Definition KALLOCBEG_MAGIC : Z := 0xcc6e96b9cc6e96b9.
Definition MALLOC_FILL_BYTE : Z := 0xbe.  Definition MALLOC_FILL_MAX : Z := 4096.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SHADOW_OFFSET : Z := 0x7fff8000.
Definition SH (a : Z) : Z := SHADOW_OFFSET + a / 8.
Definition KLOWSHADOW_BEG : Z := 0x7fff7000.   Definition KLOWSHADOW_END : Z := 0x8fff7000.
Definition KHIGHSHADOW_BEG : Z := 0x2008fff7000. Definition KHIGHSHADOW_END : Z := 0x10007fff8000.
Definition KHIGHMEM_BEG : Z := 0x10007fff8000.   Definition KHIGHMEM_END : Z := 0x7fffffffffff.
Definition addr_is_in_mem (a : Z) : Prop := (0 <= a <= SHADOW_OFFSET - 1) \/ (KHIGHMEM_BEG <= a <= KHIGHMEM_END).
(* [comment removed for export] *)
Definition SV_OK : Z := 0.        (* [comment removed for export] *)
Definition SV_HEAP_LEFT_RZ : Z := 0xfa.  Definition SV_HEAP_RIGHT_RZ : Z := 0xfb.  Definition SV_HEAP_FREED : Z := 0xfd.
Definition SV_STACK_LEFT : Z := 0xf1. Definition SV_STACK_MID : Z := 0xf2. Definition SV_STACK_RIGHT : Z := 0xf3.
Definition SV_STACK_AFTER_RETURN : Z := 0xf5. Definition SV_STACK_AFTER_SCOPE : Z := 0xf8. Definition SV_GLOBAL_RZ : Z := 0xf9.
(* [comment removed for export] *)
Definition shadow_enc (n : Z) : list Z :=
  repeat 0 (Z.to_nat (n / 8)) ++ (if (n mod 8) =? 0 then [] else [n mod 8]).
Definition clear_shadow_mmap_threshold : Z := 0x10000.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FS_LOG : Z := 20.
Definition FS_FLAGS_OFF : Z := 4096.
Definition FS_FRAMES_OFF : Z := 4096 + 2^15.            (* [comment removed for export] *)
Definition FS_TOTAL : Z := 0xb09000.
Definition fframe := (Z * Z)%type.                      (* [comment removed for export] *)
Definition fsz (k : Z) : Z := Z.shiftl 64 k.             (* [comment removed for export] *)
Definition fcap (k : Z) : Z := Z.shiftl 1 (FS_LOG - 6 - k).   (* [comment removed for export] *)
Definition fflags_off (k : Z) : Z := FS_FLAGS_OFF + Z.shiftl (Z.shiftl (Z.shiftr 1023 (10 - k)) (10 - k)) (FS_LOG - 15).
Definition fframe_addr (fs k pos : Z) : Z := fs + FS_FRAMES_OFF + Z.shiftl 1 FS_LOG * k + fsz k * pos.
Definition fflag_addr (fs k pos : Z) : Z := fs + fflags_off k + pos.
Definition fsavedflag_off (k : Z) : Z := fsz k - 8.     (* [comment removed for export] *)
Definition FF_REALSTACK_OFF : Z := 24.
Definition KFRAME_MAGIC_LIVE : Z := 0x41b58ab3.  Definition KFRAME_MAGIC_RETIRED : Z := 0x45e0360e.
Fixpoint lf_count (k : Z) (LF : list fframe) : Z :=
  match LF with [] => 0 | (_, k') :: LF' => (if k' =? k then 1 else 0) + lf_count k LF' end.
Fixpoint lf_remove (F : Z) (LF : list fframe) : list fframe :=
  match LF with [] => [] | (G, k) :: LF' => if G =? F then LF' else (G, k) :: lf_remove F LF' end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SEC_SLOT_TAX : Z := 2^19.
(* [comment removed for export] *)
Definition CL24_TAX : Z := 1572864.
Definition is_cl24 (n : Z) : bool := is_primary n && (pclass n =? 24).
Definition cost_malloc (n : Z) : Z :=
  4 * asz n + 64 + (if is_primary n then 0 else SEC_SLOT_TAX) + (if is_cl24 n then CL24_TAX else 0).
Definition cost_free : Z := 64.
Definition cost_realloc (n : Z) : Z := cost_malloc n + cost_free.
(* [comment removed for export] *)
Definition AMALLOC_STACK : Z := 8192.      (* [comment removed for export] *)
Definition ASTKMALLOC_STACK : Z := 512. (* [comment removed for export] *)
Definition AINTRIN_STACK : Z := 2304.   (* [comment removed for export] *)
Definition ASTRFN_STACK : Z := 2400.    (* [comment removed for export] *)
Definition AFORMAT_STACK : Z := 16384.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record region_st := mkRegion {
  r_allocated : Z;          (* [comment removed for export] *)
  r_mapped : Z;             (* [comment removed for export] *)
  r_mapped_fa : Z;          (* [comment removed for export] *)
  r_exhausted : bool;       (* [comment removed for export] *)
  r_fa : list Z }.          (* [comment removed for export] *)
Definition region0 : region_st := mkRegion 0 0 0 false [].

(* [comment removed for export] *)
Record qbatch := mkQB { qb_addr : Z; qb_elems : list (Z * Z) }.
Definition qb_size (b : qbatch) : Z := QBATCH_SIZE + fold_right (fun e acc => Z.max (snd e) 1 + acc) 0 (qb_elems b).
Definition qb_count (b : qbatch) : Z := Z.of_nat (length (qb_elems b)).
Definition qc_bytes (q : list qbatch) : Z := fold_right (fun b acc => qb_size b + acc) 0 q.

(* [comment removed for export] *)
Record depot_st := mkDepot {
  d_nodes : list (Z * Z * Z);   (* [comment removed for export] *)
  d_tab : Z -> Z;               (* [comment removed for export] *)
  d_nblocks : list Z;           (* [comment removed for export] *)
  d_T : Z;                      (* [comment removed for export] *)
  d_sblocks : list Z }.         (* [comment removed for export] *)
Definition d_U (d : depot_st) : Z := Z.of_nat (length (d_nodes d)).

(* [comment removed for export] *)
Definition A_DTV : Z := 0x5dc990.
Definition A_TLSBASE : Z := 0x5dd170.
Definition A_FSTLS_CELL : Z := ATP.        (* [comment removed for export] *)
(* [comment removed for export] *)
Record tls_st := mkTLS {
  tl_dtls_block : Z;   (* [comment removed for export] *)
  tl_dtls_w : Z;       (* [comment removed for export] *)
  tl_emb_d : Z;        (* [comment removed for export] *)
  tl_emb_sz : Z }.     (* [comment removed for export] *)
Definition A_EMB : Z := 0xa9228.      (* [comment removed for export] *)
Definition EMB_CAP : Z := 65536.
Definition EMB_MSG : Z := 128.         (* [comment removed for export] *)
Definition A_TOOLNAME : Z := 0xa35d0. (* [comment removed for export] *)
Definition A_ASAN_STR : Z := 0x20363.
Definition A_PRINTF_CB : Z := 0x13b6d0. (* [comment removed for export] *)
Definition A_EMB_CB : Z := 0x56a94.

Record rtstate := mkRT {
  st_sp0 : Z;                   (* [comment removed for export] *)
  st_pbase : Z;                 (* [comment removed for export] *)
  st_spacebeg : Z;              (* [comment removed for export] *)
  st_regions : list region_st;  (* [comment removed for export] *)
  st_cache_inited : bool;       (* [comment removed for export] *)
  st_cache : list (list Z);     (* [comment removed for export] *)
  st_pa : Z;                    (* [comment removed for export] *)
  st_nreserved : Z;             (* [comment removed for export] *)
  st_sec : list (Z * Z);        (* [comment removed for export] *)
  st_qthread : list qbatch;     (* [comment removed for export] *)
  st_qglobal : list qbatch;     (* [comment removed for export] *)
  st_depot : depot_st;
  st_trs : list (list Z);       (* [comment removed for export] *)
  st_trs0 : list (list Z);      (* [comment removed for export] *)
  st_fs : Z;                    (* [comment removed for export] *)
  st_hints : list Z;            (* [comment removed for export] *)
  st_lf : list fframe;          (* [comment removed for export] *)
  st_t : Z;                     (* [comment removed for export] *)
  st_ctx : Z;                   (* [comment removed for export] *)
  st_tls : tls_st;
  st_loose0 : list (Z * Z);     (* [comment removed for export] *)
  st_ia_inited : bool;          (* [comment removed for export] *)
  st_lb : list (Z * Z);         (* [comment removed for export] *)
  (* [comment removed for export] *)
  st_apend : list (Z * Z);      (* [comment removed for export] *)
  st_spend : list (Z * Z);      (* [comment removed for export] *)
  st_qpend : list (Z * Z);      (* [comment removed for export] *)
  st_qtmp : list qbatch;        (* [comment removed for export] *)
  st_qcur : list (qbatch * Z) }. (* [comment removed for export] *)
Definition PRIM_RES_SIZE : Z := 0x2000011000.   (* [comment removed for export] *)
Definition PTRARR_RES_SIZE : Z := 0x800000.
Definition PTRARR_BLOCK : Z := 0x20000.        (* [comment removed for export] *)
Definition NODEBLOCK_SIZE : Z := 0x100000.
Definition STOREBLOCK_SIZE : Z := 0x800000.
