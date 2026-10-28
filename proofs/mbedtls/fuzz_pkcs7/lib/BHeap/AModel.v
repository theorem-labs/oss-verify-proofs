(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_AModel () : Init.string Init.list := ["Corelib.Lists.ListDef.map"; "ARUN_1.chunk"; "Corelib.Numbers.BinNums.Z"; "ARUN_1.compact"; "ARUN_1.h_L"; "ARUN_1.ck_ab"; "Stdlib.Lists.List.filter"; "Corelib.Init.Datatypes.andb"; "ARUN_1.ck_prim"; "Stdlib.ZArith.BinInt.Z.eqb"; "ARUN_1.ck_cls"; "ARUN_1.h_chunks"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "ARUN_1.l_sb"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.le"; "ARUN_1.l_b6"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.add"; "ARUN_1.kHighMemBeg"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "ARUN_1.space_end"; "ARUN_1.l_top"; "ARUN_1.l_stk_hi"; "ARUN_1.l_stk_lo"; "ARUN_1.l_s0"; "ARUN_1.l_htop"; "ARUN_1.l_fs"; "ARUN_1.lowhigh"; "ARUN_1.kFakeBytes"; "ARUN_1.l_T"; "ARUN_1.l_ctx"; "ARUN_1.l_ctxlen"; "ARUN_1.l_pa"; "ARUN_1.l_nb0"; "ARUN_1.l_ss0"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.lt"; "ARUN_1.l_extra"; "ARUN_1.kNumClasses"; "ARUN_1.region"; "ARUN_1.h_reg"; "ARUN_1.region0"; "ARUN_1.r_alloc_user"; "ARUN_1.r_mapped_user"; "Stdlib.ZArith.BinInt.Z.mul"; "ARUN_1.class_size"; "ARUN_1.carved"; "ARUN_1.kUserMapSize"; "ARUN_1.kUserLimit"; "ARUN_1.r_mapped_fa"; "ARUN_1.kFreeArrayMapSize"; "ARUN_1.kFreeArraySize"; "ARUN_1.r_nfreed"; "Corelib.Init.Logic.ex"; "ARUN_1.r_fa"; "Stdlib.Lists.List.NoDup"; "ARUN_1.owned"; "Corelib.Init.Logic.iff"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.div"; "ARUN_1.wf_chunk"; "ARUN_1.h_sec"; "Corelib.Init.Datatypes.nat"; "ARUN_1.shdr"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "ARUN_1.s_chunks"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.false"; "ARUN_1.ck_map_beg"; "ARUN_1.s_map_beg"; "ARUN_1.ck_map_size"; "ARUN_1.s_map_size"; "ARUN_1.batch"; "ARUN_1.wf_batch"; "ARUN_1.q_batches"; "ARUN_1.q_bytes"; "ARUN_1.sum"; "ARUN_1.b_size"; "ARUN_1.wf_qcache"; "ARUN_1.h_tq"; "ARUN_1.kQuarantineCache"; "ARUN_1.h_gq"; "ARUN_1.kQuarantineMax"; "ARUN_1.b_addr"; "Corelib.Init.Datatypes.app"; "ARUN_1.ck_st"; "ARUN_1.CHUNK_QUARANTINE"; "Corelib.Init.Logic.unique"; "ARUN_1.ck_hdr"; "ARUN_1.b_elems"; "ARUN_1.sec"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "ARUN_1.s_nres"; "ARUN_1.kPtrArrayChunks"; "ARUN_1.h_pa_committed"; "ARUN_1.s_size"; "ARUN_1.depot"; "ARUN_1.h_dep"; "ARUN_1.d_n"; "ARUN_1.d_nb"; "ARUN_1.kDepotNodesL2"; "Corelib.Lists.ListDef.nth"; "ARUN_1.s_total"; "ARUN_1.d_bl"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.of_num_uint"; "Corelib.Init.Number.UIntDecimal"; "Corelib.Init.Decimal.D3"; "Corelib.Init.Decimal.D2"; "Corelib.Init.Decimal.D7"; "Corelib.Init.Decimal.D6"; "Corelib.Init.Decimal.D8"; "Corelib.Init.Decimal.Nil"; "ARUN_1.f_flag"; "ARUN_1.h_fake"; "Corelib.Init.Datatypes.true"; "ARUN_1.nframes"; "Corelib.Init.Datatypes.pair"; "ARUN_1.ff_addr"; "ARUN_1.ff_bytes"; "ARUN_1.CU"; "ARUN_1.CN"; "ARUN_1.CSB"; "ARUN_1.kPtrArrayCommit"; "ARUN_1.CPA"; "ARUN_1.CE"; "ARUN_1.a_sech"; "ARUN_1.h_acct"; "ARUN_1.h_havol"; "ARUN_1.SECC"; "ARUN_1.wf_L"; "ARUN_1.wf_cache"; "ARUN_1.wf_region"; "ARUN_1.wf_chunks"; "ARUN_1.wf_quar"; "ARUN_1.wf_sec"; "ARUN_1.wf_depot"; "ARUN_1.wf_budget"; "Corelib.Init.Logic.or"; "ARUN_1.rz_size"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Definition SHADOW_OFFSET : Z := 0x7fff8000.
Definition ashadow (a : Z) : Z := SHADOW_OFFSET + a / 8.          (* [comment removed for export] *)
Definition kLowMemEnd   : Z := 0x7fff7fff.
Definition kHighMemBeg  : Z := 0x10007fff8000.
Definition kHighMemEnd  : Z := 0x7fffffffffff.
Definition addr_is_in_mem (a : Z) : Prop := (0 <= a <= kLowMemEnd) \/ (kHighMemBeg <= a <= kHighMemEnd).

Definition kNumClasses      : Z := 32.
Definition kRegionSizeLog   : Z := 32.
Definition kRegionSize      : Z := 2^32.
Definition kSpaceSize       : Z := 2^37.
Definition kUserMapSize     : Z := 2^18.
Definition kFreeArrayMapSize : Z := 2^18.
Definition kFreeArrayOffset : Z := 0xE0000000.     (* [comment removed for export] *)
Definition kFreeArraySize   : Z := 0x20000000.
Definition kUserLimit       : Z := 0xE0000000.     (* [comment removed for export] *)
Definition kMaxSize         : Z := 0x10000.        (* [comment removed for export] *)
Definition kBatchClass      : Z := 24.             (* [comment removed for export] *)
Definition kBatchSize       : Z := 8192.
Definition kBatchCap        : Z := 1021.           (* [comment removed for export] *)
Definition kMinRedzone      : Z := 16.
Definition kMaxRedzone      : Z := 2048.
Definition kChunkHeaderSize : Z := 16.
Definition kAllocBegMagic   : Z := 0xCC6E96B9CC6E96B9.
Definition CHUNK_INVALID    : Z := 0.
Definition CHUNK_ALLOCATED  : Z := 2.
Definition CHUNK_QUARANTINE : Z := 3.
Definition kQuarantineMax   : Z := 0x10000000.     (* [comment removed for export] *)
Definition kQuarantineMin   : Z := 0xE666661.      (* [comment removed for export] *)
Definition kQuarantineCache : Z := 0x100000.       (* [comment removed for export] *)
Definition kMaxMallocFill   : Z := 4096.
Definition kMallocFillByte  : Z := 0xbe.
Definition kClearShadowMmapThreshold : Z := 0x10000.  (* [comment removed for export] *)
Definition kMallocContextSize : Z := 30.
Definition kStackTraceMax   : Z := 255.
Definition kMaxUserMalloc   : Z := 2^40.
Definition kPtrArrayCommit  : Z := 0x20000.        (* [comment removed for export] *)
Definition kPtrArrayChunks  : Z := 0x4000.
Definition kDepotTabBits    : Z := 20.
Definition kDepotNodesL1    : Z := 2^15.           (* [comment removed for export] *)
Definition kDepotNodesL2    : Z := 2^16.           (* [comment removed for export] *)
Definition kDepotNodeSize   : Z := 16.
Definition kDepotBlockBytes : Z := 2^20.
Definition kStoreBlockFrames : Z := 2^20.
Definition kStoreBlockBytes : Z := 2^23.
Definition kFakeLog         : Z := 20.             (* [comment removed for export] *)
Definition kFakeFlagsOffset : Z := 4096.
Definition kFakeFramesOffset : Z := 4096 + 2^15.    (* [comment removed for export] *)
Definition kFakeBytes       : Z := 0xb09000.

(* [comment removed for export] *)
Definition A_INSTANCE  : Z := 0x106398.
Definition A_SPACEBEG_CELL : Z := A_INSTANCE + 32.
Definition A_RI_CELL   : Z := A_INSTANCE + 48.
Definition A_SECONDARY : Z := A_INSTANCE + 64.
Definition A_SEC_MUTEX : Z := A_INSTANCE + 680.
Definition A_GSTATS    : Z := A_INSTANCE + 688.
Definition A_QUAR      : Z := A_INSTANCE + 728.
Definition A_Q_MAX     : Z := A_INSTANCE + 792.
Definition A_Q_MIN     : Z := A_INSTANCE + 800.
Definition A_Q_MAXCACHE : Z := A_INSTANCE + 808.
Definition A_Q_CMUTEX  : Z := A_INSTANCE + 880.
Definition A_Q_RMUTEX  : Z := A_INSTANCE + 881.
Definition A_Q_GLOBAL  : Z := A_INSTANCE + 888.    (* [comment removed for export] *)
Definition A_FB_MUTEX  : Z := A_INSTANCE + 984.
Definition A_MAXUSER   : Z := A_INSTANCE + 3616.
Definition A_MINRZ     : Z := A_INSTANCE + 3624.
Definition A_MAXRZ     : Z := A_INSTANCE + 3626.
Definition A_FLAGS     : Z := 0x1071f8.
Definition A_DEPOT     : Z := 0x1eb8d8.
Definition A_DEPOT_N   : Z := A_DEPOT + 0x400000.
Definition A_DEPOT_MAP1 : Z := A_DEPOT + 0x400010.
Definition A_STORE     : Z := 0x1db8c8.
Definition A_IA        : Z := 0x10ac00.            (* [comment removed for export] *)
Definition A_IA_INIT   : Z := 0x199488.            (* [comment removed for export] *)
Definition A_SHADOWBASE_CELL : Z := 0x1099f8.
Definition A_UAR_CELL  : Z := 0x109a00.
Definition A_TP        : Z := 0x63ca90.
Definition A_PC_MALLOC : Z := 0x69720.             (* [comment removed for export] *)
Definition A_PC_FREE   : Z := 0x695c0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition class_size (c : Z) : Z :=
  if c =? 31 then 64
  else if c <=? 16 then 32 * c
  else let k := c - 16 in
       let t := 512 * 2^(k / 2) in
       if Z.odd k then t + t / 2 else t.

(* [comment removed for export] *)
Definition class_of (s : Z) : Z :=
  if s <=? 512 then (s + 31) / 32
  else let l := Z.log2 s in
       let hbit := (s / 2^(l - 1)) mod 2 in
       let lbits := s mod 2^(l - 1) in
       16 + 2 * (l - 9) + hbit + (if lbits =? 0 then 0 else 1).

Definition max_cached (c : Z) : Z := Z.max 1 (Z.min 8 (1024 / class_size c)).
Definition max_count (c : Z) : Z := 2 * max_cached c.

(* [comment removed for export] *)
Definition rz_log (n : Z) : Z :=
  if n <? 49 then 0 else if n <? 97 then 1 else if n <? 449 then 2 else if n <? 0xf81 then 3
  else if n <? 0x3f01 then 4 else if n <? 0x7e01 then 5 else if n <? 0xfc01 then 6 else 7.
Definition rz_size (n : Z) : Z := 16 * 2^(rz_log n).
Definition round_up (x a : Z) : Z := ((x + a - 1) / a) * a.
Definition nfix (n : Z) : Z := Z.max n 1.                       (* [comment removed for export] *)
Definition rounded (n : Z) : Z := round_up (Z.max n 8) 8.
Definition needed (n : Z) : Z := rounded n + rz_size n.
Definition from_primary (n : Z) : bool := needed n <=? kMaxSize.
Definition needed2 (n : Z) : Z := if from_primary n then needed n else needed n + rz_size n.
Definition pclass (n : Z) : Z := class_of (needed n).           (* [comment removed for export] *)
Definition used_size (n : Z) : Z := nfix n.
Definition sec_map_size (n : Z) : Z := round_up (needed2 n) 4096 + 4096.

(* [comment removed for export] *)
#[using="Type"] Example class_size_tbl :
  map class_size [1;2;3;16;17;18;19;20;24;30;31] = [32;64;96;512;768;1024;1536;2048;8192;65536;64].
Proof. reflexivity. Qed.
#[using="Type"] Example class_of_tbl :
  map class_of [1;32;33;512;513;768;769;1024;8192;8200;65536] = [1;1;2;16;17;17;18;18;24;25;30].
Proof. reflexivity. Qed.
#[using="Type"] Example max_count_tbl : map max_count [1;4;5;6;7;8;9;11;16;17;24;30] = [16;16;12;10;8;8;6;4;4;2;2;2].
Proof. reflexivity. Qed.
#[using="Type"] Example needed_tbl : map needed [0;1;6;48;49;64512;64513] = [24;24;24;64;88;65536;66568].
Proof. reflexivity. Qed.
#[using="Type"] Example pclass_tbl : map pclass [1;16;17;48;49;64;65;96;97;449;3969;7937;16129;64512] = [1;1;2;2;3;3;4;4;6;17;23;25;27;30].
Proof. reflexivity. Qed.
#[using="Type"] Example sec_map_size_tbl : map sec_map_size [64513;65536;614405] = [73728;73728;626688].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record alayout := AL_ {
  l_b6 : Z;        (* [comment removed for export] *)
  l_sb : Z;        (* [comment removed for export] *)
  l_pa : Z;        (* [comment removed for export] *)
  l_T : Z;         (* [comment removed for export] *)
  l_ctx : Z;       (* [comment removed for export] *)
  l_fs : Z;        (* [comment removed for export] *)
  l_nb0 : Z;       (* [comment removed for export] *)
  l_ss0 : Z;       (* [comment removed for export] *)
  l_top : Z;       (* [comment removed for export] *)
  l_s0 : Z;        (* [comment removed for export] *)
  l_htop : Z;      (* [comment removed for export] *)
  l_stk_lo : Z;    (* [comment removed for export] *)
  l_stk_hi : Z;    (* [comment removed for export] *)
  l_errno : Z;     (* [comment removed for export] *)
  l_extra : list (Z * Z);   (* [comment removed for export] *)
  l_ctxlen : Z;    (* [comment removed for export] *)
  l_gsh : list (Z * Z)  (* [comment removed for export] *)
}.

Definition space_end (L : alayout) : Z := l_sb L + kSpaceSize.
Definition ri_base (L : alayout) : Z := space_end L.                        (* [comment removed for export] *)
Definition ri_addr (L : alayout) (c : Z) : Z := ri_base L + 128 * c.
Definition region_beg (L : alayout) (c : Z) : Z := l_sb L + c * kRegionSize.
Definition fa_beg (L : alayout) (c : Z) : Z := region_beg L c + kFreeArrayOffset.
Definition chunk_at (L : alayout) (c k : Z) : Z := region_beg L c + k * class_size c.   (* [comment removed for export] *)
Definition compact (L : alayout) (c a : Z) : Z := (a - region_beg L c) / 16.          (* [comment removed for export] *)
Definition uncompact (L : alayout) (c p : Z) : Z := region_beg L c + 16 * p.
(* [comment removed for export] *)
Definition unit_lo (L : alayout) (j : Z) : Z := l_sb L + j * kUserMapSize.
Definition kNumUnits : Z := kSpaceSize / kUserMapSize.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_qcache (L : alayout) : Z := l_T L + 80.       (* [comment removed for export] *)
Definition t_cache (L : alayout) : Z := l_T L + 208.
Definition t_pclass (L : alayout) (c : Z) : Z := t_cache L + 80 * c.   (* [comment removed for export] *)
Definition t_cstats (L : alayout) : Z := t_cache L + 2560.
Definition t_stats (L : alayout) : Z := l_T L + 2800.
Definition t_unwinding (L : alayout) : Z := l_T L + 3168.

(* [comment removed for export] *)
Definition nframes (k : Z) : Z := 2^(14 - k).
Definition ff_bytes (k : Z) : Z := 64 * 2^k.
Definition ff_flags (L : alayout) (k : Z) : Z := l_fs L + kFakeFlagsOffset + (2^15 - 2^(15 - k)).  (* [comment removed for export] *)
Definition ff_flag (L : alayout) (k i : Z) : Z := ff_flags L k + i.
Definition ff_addr (L : alayout) (k i : Z) : Z := l_fs L + kFakeFramesOffset + k * 2^kFakeLog + i * ff_bytes k.
Definition ff_hint (L : alayout) (k : Z) : Z := l_fs L + 8 * k.

#[using="Type"] Example ff_flags_tbl : map (fun k => ff_flags (AL_ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 [] 0 []) k - 4096) [0;1;2;5;10] = [0;16384;24576;31744;32736].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition dep_bucket (h : Z) : Z := A_DEPOT + 4 * (h mod 2^kDepotTabBits).
Definition dep_map1 (k : Z) : Z := A_DEPOT_MAP1 + 8 * k.
Definition dep_node (blk : Z) (id : Z) : Z := blk + kDepotNodeSize * (id mod kDepotNodesL2).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region := RG {
  r_mapped_user : Z;
  r_alloc_user : Z;
  r_mapped_fa : Z;
  r_fa : list Z          (* [comment removed for export] *)
}.
Definition r_nfreed (r : region) : Z := Z.of_nat (length (r_fa r)).
Definition region0 : region := RG 0 0 0 [].

Record pcl := PC {
  pc_max : Z;            (* [comment removed for export] *)
  pc_csize : Z;
  pc_chunks : list Z     (* [comment removed for export] *)
}.
Definition pc_count (p : pcl) : Z := Z.of_nat (length (pc_chunks p)).
Definition pcl0 : pcl := PC 0 0 [].

(* [comment removed for export] *)
Record chunk := CK {
  ck_ab : Z;             (* [comment removed for export] *)
  ck_n : Z;              (* [comment removed for export] *)
  ck_prim : bool;
  ck_cls : Z;            (* [comment removed for export] *)
  ck_st : Z              (* [comment removed for export] *)
}.
Definition ck_rz (k : chunk) : Z := rz_size (ck_n k).
Definition ck_user (k : chunk) : Z := ck_ab k + ck_rz k.
Definition ck_hdr (k : chunk) : Z := ck_user k - kChunkHeaderSize.
Definition ck_map_beg (k : chunk) : Z := ck_ab k - 4096.
Definition ck_map_size (k : chunk) : Z := sec_map_size (ck_n k).
(* [comment removed for export] *)
Definition ck_end (k : chunk) : Z :=
  if ck_prim k then ck_ab k + class_size (ck_cls k) else ck_map_beg k + ck_map_size k.

Record batch := BA {
  b_addr : Z;            (* [comment removed for export] *)
  b_elems : list Z;      (* [comment removed for export] *)
  b_size : Z             (* [comment removed for export] *)
}.
Definition b_count (b : batch) : Z := Z.of_nat (length (b_elems b)).

Record qcache := QC { q_batches : list batch; q_bytes : Z }.
Definition qcache0 : qcache := QC [] 0.

Record shdr := SH { s_map_beg : Z; s_map_size : Z; s_size : Z }.   (* [comment removed for export] *)
Record sec := SE { s_chunks : list shdr; s_nres : Z }.
Definition sec0 : sec := SE [] 0.

(* [comment removed for export] *)
Record depot := DP {
  d_n : Z;                     (* [comment removed for export] *)
  d_nb : list Z;               (* [comment removed for export] *)
  s_total : Z;                 (* [comment removed for export] *)
  d_bl : list Z                (* [comment removed for export] *)
}.

Record fake := FK {
  f_hint : Z -> Z;             (* [comment removed for export] *)
  f_flag : Z -> Z -> bool      (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record acct := AC {
  a_sech : list (Z * Z);       (* [comment removed for export] *)
  (* [comment removed for export] *)
  a_emb : Z;                   (* [comment removed for export] *)
  a_esz : Z;                   (* [comment removed for export] *)
  a_exh : Z -> bool            (* [comment removed for export] *)
}.

Record ahst := AH {
  h_L : alayout;
  h_reg : Z -> region;
  h_cache : Z -> pcl;
  h_cinit : bool;              (* [comment removed for export] *)
  h_chunks : list chunk;       (* [comment removed for export] *)
  h_tq : qcache;               (* [comment removed for export] *)
  h_gq : qcache;               (* [comment removed for export] *)
  h_sec : sec;
  h_dep : depot;
  h_ia : bool;                 (* [comment removed for export] *)
  h_fake : fake;
  h_pa_committed : Z;          (* [comment removed for export] *)
  h_havol : Z;                 (* [comment removed for export] *)
  h_acct : acct
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition live (h : ahst) : list chunk := filter (fun k => ck_st k =? CHUNK_ALLOCATED) (h_chunks h).
Definition quar (h : ahst) : list chunk := filter (fun k => ck_st k =? CHUNK_QUARANTINE) (h_chunks h).
(* [comment removed for export] *)
Definition blocks (h : ahst) : list (Z * Z) := map (fun k => (ck_user k, ck_n k)) (live h).

(* [comment removed for export] *)
Definition carved (h : ahst) (c : Z) : Z := r_alloc_user (h_reg h c) / class_size c.

(* [comment removed for export] *)
Definition fa_set (h : ahst) (c : Z) : list Z := r_fa (h_reg h c).
Definition cache_set (h : ahst) (c : Z) : list Z := pc_chunks (h_cache h c).
Definition chunk_set (h : ahst) (c : Z) : list Z := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "(0.$1.$2.Lk,$1.(3.(4.O2.)O1.(5.R1.))(6.$1.Lk,$1.(7.(8.R1.)(9.(:.R1.)O1.))(;.O2.)))")
(* [comment removed for export] *).
Definition batch_set (h : ahst) (c : Z) : list Z :=
  if c =? kBatchClass then map (fun b => compact (h_L h) c (b_addr b)) (q_batches (h_tq h) ++ q_batches (h_gq h)) else [].
Definition owned (h : ahst) (c : Z) : list Z := fa_set h c ++ cache_set h c ++ chunk_set h c ++ batch_set h c.

Definition sum (l : list Z) : Z := fold_right Z.add 0 l.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lowhigh (X n : Z) : Prop :=
  0x1000 <= X /\ (X + n <= 0x10000 \/ 0x65f000 <= X) /\ (X + n <= 0x7fff7000 \/ kHighMemBeg <= X).
#[using="Type"] Lemma lowhigh_big : forall X n, lowhigh X n -> 0xF000 < n -> 0x65f000 <= X.
Proof. (intros X n dd_H; ddestruct dd_H as (A & B & _); intros N). lia. Qed.


Definition wf_L (L : alayout) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "(<.(=.$2.(>.(?.O1.)(10.+2.+10.))=)(<.(11.(12.O1.)(13.(?.O1.)=))(<.(11.(?.O1.)(14.(12.O1.)(10.+2.+10.)))(<.(=.$2.(>.(12.O1.)+1000.)=)(<.(11.$15.(12.O1.))(<.(11.(14.(12.O1.)+2000011000.)(16.VhAR,))(<.(11.(14.(17.O1.)+1000.)(14.(12.O1.)+2000011000.))(<.(=.$2.(>.(18.O1.)+1000.)=)(<.(11.(10.+2.+17.)(18.O1.))(<.(11.(18.O1.)(19.O1.))(<.(=.$2.(1:.O1.)(13.(1;.O1.)(10.+2.+17.)))(<.(11.(13.(1;.O1.)+:0.)(18.O1.))(<.(11.(14.(1:.O1.)+1000.)(1<.O1.))(<.(11.(14.(1<.O1.)+10.)(19.O1.))(<.(=.$2.(>.(1<.O1.)+10.)=)(<.(=.$2.(>.(1:.O1.)+10.)=)(<.(11.(16.VhAR,)(1:.O1.))(<.(11.(19.O1.)(10.+2.+2?.))(<.(=.$2.(>.(19.O1.)+1000.)=)(<.(=.$2.(>.(1=.O1.)+1000.)=)(<.(1>.(1=.O1.)$1?.)(<.(11.(14.(1=.O1.)$1?.)(16.VhAR,))(<.(=.$2.(>.(20.O1.)+1000.)=)(<.(1>.(20.O1.)+1000.)(<.(11.(14.(20.O1.)+1000.)(16.VhAR,))(<.(1>.(21.O1.)+10000.)(<.(11.(14.(21.O1.)(22.O1.))(16.VhAR,))(<.(=.$2.(22.O1.)+10000.)(<.(=.$2.(>.(21.O1.)+1000.)=)(<.(=.$2.(>.(23.O1.)+1000.)=)(<.(1>.(23.O1.)+800000.)(<.(11.(14.(23.O1.)+800000.)(16.VhAR,))(<.(=.$2.(>.(24.O1.)+1000.)=)(<.(=.$2.(>.(25.O1.)+1000.)=)(26.(27.$2.$2.)Lr,(27.$2.$2.)(<.(1>.(28.$2.$2.R1.)(29.$2.$2.R1.))(<.(2:.=(29.$2.$2.R1.))(<.(11.(14.(28.$2.$2.R1.)(29.$2.$2.R1.))(16.VhAR,))(<.(=.$2.(>.(28.$2.$2.R1.)+1000.)=)(=.$2.(>.(29.$2.$2.R1.)+1000.)=)))))(2;.O1.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition wf_cache (h : ahst) : Prop :=
  forall c, 0 <= c < kNumClasses ->
    let p := h_cache h c in
    (if h_cinit h then (1 <= c -> pc_max p = max_count c /\ pc_csize p = class_size c) else pc_max p = 0 /\ pc_csize p = 0)
    /\ (c = 0 -> pc_chunks p = [])
    /\ pc_count p <= Z.max (pc_max p) 0 /\ pc_count p <= 16
    /\ Forall (fun q => 0 <= q /\ exists k, 0 <= k < carved h c /\ 16 * q = k * class_size c) (pc_chunks p).

Definition wf_region (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "Pc,$2.P,(<.(11.=R1.)(2:.R1.$2<.))Zr,$2=.(2>.O1.R2.)(<.P,(=.$2.R3.=)(=.$2=.R2.$2?.)(<.(<.(11.=(30.R1.))(11.(30.R1.)(31.R1.)))(<.(=.$2.(30.R1.)(32.(33.R3.)(34.O1.R3.)))(<.(=.$2.(>.(31.R1.)$35.)=)(<.(11.(31.R1.)$36.)(<.P,(11.+1.R3.)(11.(13.(31.R2.)(30.R2.))(10.+2.+13.))(<.(=.$2.(>.(37.R1.)$38.)=)(<.(<.(11.=(37.R1.))(11.(37.R1.)$39.))(<.(11.(32.+4.(3:.R1.))(37.R1.))(<.(26.$2.Lq,$2.(<.(11.=R1.)(3;.$2.Lk,$2.(<.(<.(11.=R1.)(2:.R1.(34.O1.R5.)))(=.$2.(32.+10.R2.)(32.R1.(33.R5.))))))(3<.R1.))(<.(3=.$2.(3>.O1.R3.))Pk,$2.(3?.(<.(11.=R1.)(2:.R1.(34.O1.R4.)))(40.$2.(41.(32.R1.(33.R4.))+10.)(3>.O1.R4.))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

Definition wf_chunk (L : alayout) (S : sec) (k : chunk) : Prop :=
  1 <= ck_n k < 2^40
  /\ (ck_st k = CHUNK_ALLOCATED \/ ck_st k = CHUNK_QUARANTINE)
  /\ (ck_prim k = from_primary (ck_n k))
  /\ (if ck_prim k
      then ck_cls k = pclass (ck_n k) /\ 1 <= ck_cls k <= 30
           /\ exists i, 0 <= i /\ ck_ab k = chunk_at L (ck_cls k) i
      else exists i, nth_error (s_chunks S) i = Some (SH (ck_map_beg k) (ck_map_size k) (needed2 (ck_n k)))
           /\ ck_map_beg k mod 4096 = 0 /\ 0 < ck_map_beg k /\ ck_map_beg k + ck_map_size k <= ACEIL
           /\ (ck_map_beg k + ck_map_size k <= SHADOW_OFFSET - 4096 \/ kHighMemBeg <= ck_map_beg k)).

Definition wf_chunks (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "(<.(26.$1.(42.(4.O1.)(43.O1.))(;.O1.))(<.(3=.$2.(0.$1.$2.$5.(;.O1.)))Pi,$44.Psh,$45.P,(=.(46.$45.)(47.$45.(48.(43.O1.))R2.)(49.$45.R1.))(3;.$1.Lk,$1.(<.(40.$1.R1.(;.O1.))(<.(=.$4:.(8.R1.)$4;.)(<.(=.$2.(4<.R1.)(4=.R3.))(=.$2.(4>.R1.)(4?.R3.))))))))")
(* [comment removed for export] *).

Definition wf_batch (h : ahst) (b : batch) : Prop :=
  1 <= b_count b <= kBatchCap
  /\ b_size b = kBatchSize + sum (map (fun e => match find (fun k => ck_hdr k =? e) (h_chunks h) with Some k => used_size (ck_n k) | None => 0 end) (b_elems b))
  /\ Forall (fun e => exists k, In k (h_chunks h) /\ ck_st k = CHUNK_QUARANTINE /\ ck_hdr k = e) (b_elems b)
  /\ (exists i, 0 <= i < carved h kBatchClass /\ b_addr b = chunk_at (h_L h) kBatchClass i).

Definition wf_qcache (h : ahst) (q : qcache) (cap : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "(<.(26.$50.(51.O3.)(52.O2.))(<.(=.$2.(53.O2.)(54.(0.$50.$2.$55.(52.O2.))))(<.(11.=(53.O2.))(11.(53.O2.)O1.))))")
(* [comment removed for export] *).

Definition wf_quar (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "(<.(56.O1.(57.O1.)$58.)(<.(56.O1.(59.O1.)$5:.)(<.(3=.$2.(0.$50.$2.$5;.(5<.$50.(52.(57.O1.))(52.(59.O1.)))))Pk,$1.P,(40.$1.R1.(;.O1.))P,(=.$2.(5=.R2.)$5>.)(3;.$50.(5?.$50.Lb,$50.(<.(40.$50.R1.(5<.$50.(52.(57.O1.))(52.(59.O1.))))(40.$2.(60.R4.)(61.R1.))))))))")
(* [comment removed for export] *).

Definition wf_sec (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "ZS,$62.(43.O1.)(<.(11.(63.(64.$45.(48.R1.)))(65.R1.))(<.(=.$2.(>.(65.R1.)$66.)=)(<.(11.=(65.R1.))(<.(11.(32.+8.(65.R1.))(10.+2.+17.))(<.(=.$2.(67.O1.)(32.+8.(65.R1.)))(<.(2:.(63.(64.$45.(48.R1.)))(10.+2.+14.))(<.(3=.$2.(0.$45.$2.$4=.(48.R1.)))(26.$45.Lsh,$45.(<.(=.$2.(>.(4?.R1.)+1000.)=)(<.(2:.+1000.(4?.R1.))(2:.=(68.R1.))))(48.R1.)))))))))")
(* [comment removed for export] *).

Definition wf_depot (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "ZD,$69.(6:.O1.)(<.(11.+1.(6;.R1.))(<.(11.(14.(6;.R1.)+2.)(13.(10.+2.+1?.)(10.+2.+1<.)))(<.(=.$2.(63.(64.$2.(6<.R1.)))(14.(41.(6;.R1.)$6=.)+1.))(<.(26.$2.Lb,$2.(<.(11.+65?000.R1.)(<.(11.(14.R1.(10.+2.+14.))(16.VhAR,))(=.$2.(>.R1.+1000.)=)))(6<.R1.))(<.(=.$2.(6>.$2.#0.(6<.R1.)=)(24.(4.O1.)))(<.(11.=(6?.R1.))(<.(11.(14.(6?.R1.)+80.)(10.+2.+20.))(<.(=.$2.(63.(64.$2.(70.R1.)))(41.(13.(14.(6?.R1.)(10.+2.+14.))+1.)(10.+2.+14.)))(<.(26.$2.Lb,$2.(<.(11.+65?000.R1.)(<.(11.(14.R1.(10.+2.+17.))(16.VhAR,))(=.$2.(>.R1.+1000.)=)))(70.R1.))(<.(71.(64.$2.(6<.R1.))(72.(73.(74.(75.(76.(77.(78.$79.))))))))(<.(71.(64.$2.(70.R1.))#1000.)(=.$2.(6>.$2.#0.(70.R1.)=)(25.(4.O1.))))))))))))))")
(* [comment removed for export] *).

Definition wf_fake (h : ahst) (LF : list (Z * Z)) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "(<.Pk,$2.Pi,$2.P,(=.$4:.(7:.(7;.O2.)R2.R1.)$7<.)(<.(<.(11.=R3.)(11.R3.+:.))(<.(11.=R2.)(2:.R2.(7=.R3.))))(<.PA,$2.Pn,$2.(3?.(40.(27.$2.$2.)(7>.$2.$2.R2.R1.)O1.)(3;.$2.Lk,$2.(3;.$2.Li,$2.(<.(=.$4:.(7:.(7;.O2.)R2.R1.)$7<.)(<.(=.$2.R4.(7?.(4.O2.)R2.R1.))(=.$2.R3.(80.R2.)))))))(3=.$2.(0.(27.$2.$2.)$2.(28.$2.$2.)O1.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AVOL_MAX : Z := 2^37.
Definition AVOL_CALL : Z := 1024.
Definition charge_malloc (n : Z) : Z := 2 * n + AVOL_CALL.
Definition charge_free : Z := AVOL_CALL.

(* [comment removed for export] *)
Definition npg_shadow (len : Z) : Z := len / 32768 + 3.          (* [comment removed for export] *)
Definition sec_cost_live (sh : shdr) : Z := s_map_size sh + 4096 * npg_shadow (s_map_size sh).
Definition sec_cost_ghost (g : Z * Z) : Z := snd g + 4096 * npg_shadow (snd g).   (* [comment removed for export] *)
Definition SECC (h : ahst) : Z :=
  sum (map sec_cost_live (s_chunks (h_sec h))) + sum (map sec_cost_ghost (a_sech (h_acct h))).

(* [comment removed for export] *)
Definition CU  : Z := kUserMapSize + 4096 * npg_shadow kUserMapSize.          (* [comment removed for export] *)
Definition CN  : Z := kDepotBlockBytes + 4096 * npg_shadow kDepotBlockBytes.  (* [comment removed for export] *)
Definition CSB : Z := 4096 * (npg_shadow kStoreBlockBytes + (kStoreBlockBytes / 4096 + 1)).   (* [comment removed for export] *)
Definition CPA : Z := kPtrArrayCommit + 4096 * npg_shadow kPtrArrayCommit.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kEmbBytes : Z := 0x10000.
Definition CE  : Z := kEmbBytes + 4096 * npg_shadow kEmbBytes.                      (* [comment removed for export] *)
Definition ABS : Z := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "(14.(14.(14.(14.(32.+1?.(14.(32.(14.(41.$36.$35.)(41.$39.$38.))$81.)(32.(32.+2.+3.)+1000.)))(32.+8001.$82.))(32.+1000.$83.))(32.(41.(10.+2.+17.)$84.)$85.))$86.)")
(* [comment removed for export] *).
#[using="Type"] Example costs_tbl : (CU, CN, CSB, CPA) = (307200, 1191936, 9453568, 159744). Proof. reflexivity. Qed.
#[using="Type"] Example abs_fits : ABS + AVOL_MAX + 2^34 <= 2^39. Proof. cbv; discriminate. Qed.   (* [comment removed for export] *)
#[using="Type"] Example abs_fits2 : ABS + AVOL_MAX + 2^35 <= 2^39. Proof. cbv; discriminate. Qed.  (* [comment removed for export] *)

Definition wf_budget (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "(<.(26.(27.$2.$2.)Lg,(27.$2.$2.)(<.(11.=(28.$2.$2.R1.))(<.(2:.=(29.$2.$2.R1.))(11.(14.(28.$2.$2.R1.)(29.$2.$2.R1.))(16.VhAR,))))(87.(88.O1.)))(<.(11.=(89.O1.))(11.(8:.O1.)(89.O1.))))")
(* [comment removed for export] *).

Definition awf (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AModel ()) "(<.(8;.(4.O1.))(<.(8<.O1.)(<.(8=.O1.)(<.(8>.O1.)(<.(8?.O1.)(<.(90.O1.)(<.(91.O1.)(92.O1.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


#[using="Type"] Lemma rz_size_cases : ltac2:(CDefT.buildp (gd_tbl_AModel ()) "Pn,$2.(93.(=.$2.(94.R1.)+10.)(93.(=.$2.(94.R1.)+20.)(93.(=.$2.(94.R1.)+40.)(93.(=.$2.(94.R1.)+80.)(93.(=.$2.(94.R1.)+100.)(93.(=.$2.(94.R1.)+200.)(93.(=.$2.(94.R1.)+400.)(=.$2.(94.R1.)+800.))))))))")
(* [comment removed for export] *).
Proof. intros n. unfold rz_size, rz_log. repeat (destruct (_ <? _)); cbn; lia. Qed.

#[using="Type"] Lemma round_up_spec : forall x a, 0 < a -> x <= round_up x a < x + a /\ round_up x a mod a = 0.
Proof.
  intros x a Ha. unfold round_up.
  pose proof (Z.div_mod (x + a - 1) a ltac:(lia)). pose proof (Z.mod_pos_bound (x + a - 1) a Ha).
  split; [nia|]. apply Z_mod_mult.
Qed.

#[using="Type"] Lemma round_up_le : forall x a b, 0 < a -> x <= b -> b mod a = 0 -> round_up x a <= b.
Proof.
  intros x a b Ha Hx Hb. unfold round_up.
  pose proof (Z.div_mod b a ltac:(lia)) as E. rewrite Hb, Z.add_0_r in E.
  assert (Hq : (x + a - 1) / a <= (b / a * a + (a - 1)) / a) by (apply Z.div_le_mono; lia).
  rewrite Z.div_add_l in Hq by lia. rewrite (Z.div_small (a - 1) a) in Hq by lia.
  nia.
Qed.

#[using="Type"] Lemma rounded_spec : forall n, 0 <= n -> Z.max n 8 <= rounded n < Z.max n 8 + 8 /\ rounded n mod 8 = 0.
Proof. intros. unfold rounded. apply round_up_spec. lia. Qed.

#[using="Type"] Lemma rounded_le : forall n b, Z.max n 8 <= b -> b mod 8 = 0 -> rounded n <= b.
Proof. intros. unfold rounded. apply round_up_le; lia. Qed.


#[using="Type"] Lemma from_primary_iff : forall n, 0 <= n -> (from_primary n = true <-> n <= 64512).
Proof.
  intros n Hn. unfold from_primary, needed, kMaxSize, rz_size, rz_log.
  destruct (rounded_spec n Hn) as [R _].
  assert (R2 : n <= 64512 -> rounded n <= 64512) by (intros; apply rounded_le; [lia|reflexivity]).
  destruct (Z.ltb_spec0 n 49); [|destruct (Z.ltb_spec0 n 97); [|destruct (Z.ltb_spec0 n 449);
    [|destruct (Z.ltb_spec0 n 0xf81); [|destruct (Z.ltb_spec0 n 0x3f01); [|destruct (Z.ltb_spec0 n 0x7e01);
    [|destruct (Z.ltb_spec0 n 0xfc01)]]]]]]; cbn -[rounded Z.max Z.add Z.leb];
  (split; intros H; [apply (proj1 (Z.leb_le _ _)) in H | apply (proj2 (Z.leb_le _ _))]; lia).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma class_size_pos : forall c, 1 <= c <= 31 -> 32 <= class_size c.
Proof.
  intros c Hc. unfold class_size.
  destruct (Z.eqb_spec c 31); [lia|]. destruct (Z.leb_spec c 16); [lia|].
  assert (H0 : 0 <= (c - 16) / 2) by (apply Z.div_pos; lia).
  assert (H1 : 1 <= 2 ^ ((c - 16) / 2)).
  { change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia. }
  assert (H2 : 0 <= 512 * 2 ^ ((c - 16) / 2) / 2) by (apply Z.div_pos; lia).
  destruct (Z.odd (c - 16)); lia.
Qed.

End ARUN_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Pimg X n := (0x1000 <= X /\ (X + n <= 0x10000 \/ 0x65f000 <= X))%Z.
Notation Pband X n := (X + n <= 0x7fff7000 \/ 0x10007fff8000 <= X)%Z.
Notation Timg T := (Pimg T 4096).
Notation Tband T := (Pband T 4096).
Lemma lowhigh_Pimg : forall X n, lowhigh X n -> Pimg X n.
Proof. (intros X n dd_H; ddestruct dd_H as (A & B & C)). split; [exact A| exact B]. Qed.
Lemma lowhigh_Pband : forall X n, lowhigh X n -> Pband X n.
Proof. (intros X n dd_H; ddestruct dd_H as (A & B & C)). unfold kHighMemBeg in C. exact C. Qed.
(* [comment removed for export] *)
