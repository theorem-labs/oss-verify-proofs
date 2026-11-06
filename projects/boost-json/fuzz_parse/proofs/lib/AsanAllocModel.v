(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import FMapPositive.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hcdkShadowOffset46Stdlib6ZArith6BinInt1Zmd3submd3powmd3addmd3divmd3mul37Corelib4Init9Datatypesq34boolmd3lebq34andbq33orbhcbkHighMemBeghcbkHighMemEndhcakLowMemEndmd4log2q33natmd6to_natmd3eqbmd3oddmd6shiftlmd4landhc3msbmd3ltbmd6shiftrmd3maxmd3minhcaclass_sizehcfmax_cached_hinthcekMaxRedzoneLoghcekMinRedzoneLoghc6rz_loghc3reqhc8kMaxSizehc5mkReqhc8round_uphc7rz_sizehch1kMaxAllowedMallochc4rq_nhc9rq_neededhc7rq_sizehc6regionq33nilhc8mkRegionhc6pclasshc4mkPChc5chunkq34negbhc8ch_classhcbch_user_beghch0kChunkHeaderSizehc6qcachehc|41m1k1Q1Chc6qbatchhc6astatehcaas_regionshc7region0hc4zidxhc4znthhc8as_cachehcfas_cache_initedhc9as_chunkshc6as_envhc5as_gqhch0as_internal_inithc7as_mapshcdas_n_reservedhccas_ptr_arrayhc9as_qcachehc7as_qmaxhc7as_qminhc6as_sechc9as_shadowhccas_space_beghc5as_tqhcfas_track_shadowhc7mkStatehc7upd_nthhc7pclass0q34trueq34listhc6schunk46Stdlib5FSetscFMapPositivebPositiveMapjr71thc7mappingq34conshc7mp_base36Stdlib5Lists4Listjve6filterq34prodq34pair08positivemd6to_posq36optionq34Nonehc4ckeyjr74findjr76removehcaset_chunksjr73addjr73keyq33snd37Corelib5Lists7ListDefko63mapjr78elementshcekRegionSizeLoghch0kFreeArrayOffsethcaregion_beghch0kCompactPtrScalehcakSpaceSizehc6effectq34Somehceaddr_is_in_memhc9kPageSizehcdmem_to_shadowhc5EMmaphc7EPoisonhc8MAP_PAFNhc7PROT_RWhch9kClearShadowMmapThresholdhc5painthcaround_downhch0set_cache_initedhc5mkindq35falsehc7MAP_PAFhc7add_maphc5mkMaphch4rg_mapped_free_arrayq33apphceMkFreeArrayMaphcffree_array_basehcaget_regionhch9kAsanHeapLeftRedzoneMagichch1kFreeArrayMapSizehcekFreeArraySizehc9map_fixedhcdpoison_shadowhch1rg_allocated_userhcdrg_free_arrayhcerg_mapped_userhccrg_num_freedhcaset_regionhc9MkUserMaphc9carve_aschch7ensure_free_array_spacehcckUserMapSizeko66firstnko65skipnhch3populate_free_arrayhc8pc_counthcfcompact_to_addrhch3ensure_cache_initedhch2get_from_allocatorhc6get_pchcbkNumClasseshc9max_counthc9pc_chunkshc6set_pchcfaddr_to_compacthch3return_to_allocatorhcasc_map_beghcanearest_lehcbsc_map_size37Corelib4Init3Natoh73subhc4mkSCq36lengthhc7EMunmaphccfind_sec_idxhcaremove_maphc7set_sechcdclass_of_addrhcain_primaryhc7sc_sizehc5rq_rzhcaCAllocatedhc5EFillhc8EShadow1hch7actually_allocated_sizehcbcache_allochc8class_idhcbcompute_reqhcfkMallocFillBytehch2kMaxMallocFillSizehcelarge_allocatehc7mkChunkhcarq_primaryhccsize_too_bighc9upd_chunkmd4lnothcbam_malloc_khc7pop_envhccch_alloc_beghc6cstatehccremove_chunkhcdcache_deallochc8ch_statehc7ch_usedhcafind_chunkhch0large_deallocatehch5large_get_block_beginq31Shch1merge_batches_auxhc8qc_byteshc7qc_listjve3revhcado_recyclehcakBatchSizehcdmerge_batcheshc9pop_whilehc6set_gqhc4zlenhc7qcache0hch2quarantine_recyclehc6set_tqhc4mkQBhc8qb_countjve4lasthcbkBatchClasshcbkBatchCounthc7qb_addrhc9qb_chunkshc7qb_sizehccch_chunk_beghch2kAsanHeapFreeMagichch0quarantine_drainhch2quarantine_enqueuehc9PROT_NONEhc7zrepeathch4MkPrimaryReservationhch5MkPtrArrayReservationhccMkRegionInfohch0kPtrArrayReservejr75emptyhccinit_state_qhcdkMaxCacheSizehch2kQuarantineMaxSizehch2kQuarantineMinSizehcainit_statehceam_malloc_fullhc8ex_state" s.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kShadowOffset      : Z := 0x7fff8000.          (* [comment removed for export] *)
Definition kHighMemEnd        : Z := 0x7fffffffffff.      (* [comment removed for export] *)
Definition kHighMemBeg        : Z := 0x10007fff8000.      (* [comment removed for export] *)
Definition kLowMemEnd : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!ld!o5@2$1$0+1").
Definition kSpaceSize : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!ob@2$0+2+i5").
Definition kRegionSizeLog     : Z := 32.
Definition kRegionSize : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!ob@2$0+2+i0").
Definition kFreeArrayOffset   : Z := 0xE0000000.          (* [comment removed for export] *)
Definition kFreeArraySize     : Z := 0x20000000.
Definition kUserMapSize       : Z := 0x40000.
Definition kFreeArrayMapSize  : Z := 0x40000.
Definition kNumClasses        : Z := 32.
Definition kMaxSize           : Z := 0x10000.
Definition kCompactPtrScale   : Z := 4.
Definition kPageSize          : Z := 4096.
Definition kChunkHeaderSize   : Z := 16.
Definition kMinRedzoneLog     : Z := 0.                   (* [comment removed for export] *)
Definition kMaxRedzoneLog     : Z := 7.                   (* [comment removed for export] *)
Definition kMaxAllowedMalloc : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!ob@2$0+2+i8").                (* [comment removed for export] *)
Definition kMaxMallocFillSize : Z := 4096.                (* [comment removed for export] *)
Definition kMallocFillByte    : Z := 0xbe.
Definition kClearShadowMmapThreshold : Z := 0x10000.      (* [comment removed for export] *)
Definition kQuarantineMaxSize : Z := 0x10000000.          (* [comment removed for export] *)
Definition kQuarantineMinSize : Z := 0xE666661.           (* [comment removed for export] *)
Definition kMaxCacheSize      : Z := 0x100000.            (* [comment removed for export] *)
Definition kBatchSize         : Z := 8192.                (* [comment removed for export] *)
Definition kBatchCount        : Z := 1021.                (* [comment removed for export] *)
Definition kBatchClass        : Z := 24.                  (* [comment removed for export] *)
Definition kChunksBlockCount  : Z := 0x4000.              (* [comment removed for export] *)
Definition kMaxNumChunks : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!ob@2$0+2+h4").
Definition kPtrArrayReserve   : Z := 0x800000.

(* [comment removed for export] *)
Definition kAsanHeapLeftRedzoneMagic : Z := 0xfa.
Definition kAsanHeapFreeMagic        : Z := 0xfd.

(* [comment removed for export] *)
Definition PROT_NONE : Z := 0.  Definition PROT_RW : Z := 3.
Definition MAP_PA    : Z := 0x22.    (* [comment removed for export] *)
Definition MAP_PAF   : Z := 0x32.    (* [comment removed for export] *)
Definition MAP_PAFN  : Z := 0x4032.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition round_up : ltac2:(zQ "10!h9>1x$0>1a$0$0") := ltac2:(zQ "50!h9!p1!p7!pd!o5\1x$0\1a$0@2$3@2$2@2$4@2$1^2^1+1^1^1").
Definition round_down : ltac2:(zQ "10!h9>1x$0>1a$0$0") := ltac2:(zQ "30!h9!p7!pd\1x$0\1a$0@2$2@2$1^2^1^1").
Definition mem_to_shadow : ltac2:(zQ "10!h9>1a$0$0") := ltac2:(zQ "40!h9!ld!p1!p7\1a$0@2$2$1@2$3^1+8").
Definition addr_is_in_mem : ltac2:(zQ "20!rb!h9>1a$1$0") := ltac2:(zQ "70!s2!s8!sf!h9!t5!u3!v1\1a$3@2$2@2$1@2$0Z^1@2$0^1$6@2$1@2$0$4^1@2$0^1$5").

(* [comment removed for export] *)
Definition msb : ltac2:(zQ "10!h9>1x$0$0") := ltac2:(zQ "20!h9!ve\1x$0@1$1^1").

(* [comment removed for export] *)
Fixpoint znth {A} (l : list A) (i : nat) (d : A) : A :=
  match l, i with
  | [], _ => d
  | x :: _, O => x
  | _ :: r, S i' => znth r i' d
  end.
Fixpoint upd_nth {A} (l : list A) (i : nat) (x : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: r, O => x :: r
  | y :: r, S i' => y :: upd_nth r i' x
  end.
Definition zidx : ltac2:(zQ "20!hg5!h9>1i$1$0") := ltac2:(zQ "20!h9!hgb\1i$0@1$1^1").
Fixpoint zrepeat {A} (x : A) (n : nat) : list A := match n with O => [] | S n' => x :: zrepeat x n' end.
Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition class_size : ltac2:(zQ "10!h9>1c$0$0") := ltac2:(zQ "a0!rb!h9!p7!o5!p1!hh4!s2!pd!hha!hi0\1c$1M0\0$0$1@2$5^1+hf+k0M0\0$0$1@2$6^1+h0@2$7+i0^1=1t$1@2$9+ig0@2$2@2$3^1+h0+2M0\0$0$1@1$8@2$3^2+h0@2$4^1@2$2^1+2^1").

(* [comment removed for export] *)
Definition class_id : ltac2:(zQ "10!h9>1s$0$0") := ltac2:(zQ "b0!h9!rb!p1!o5!hi9!hi0!hj0!p7!s2!hj6!hjc\1s$0M1\0$1$0@2$8^1+ig0@2$7@2$2^1+hf+i0=1l$0@1$6^1=5hbits$0@2$4@2$a^2@2$3^1+1+1=5lbits$0@2$4^3@2$3@2$5+1@2$3^2+1+1@2$2@2$2@2$2+h0@2$5@2$3^3+9+1^2M1\0$1$0@2$9Z^1+1Z").

(* [comment removed for export] *)
Definition max_cached_hint : ltac2:(zQ "10!h9>2sz$0$0") := ltac2:(zQ "60!h9!rb!p7!hh4!hk5!hkb\2sz$0M1\0$1$0@2$3^1ZZ=1n$0@2$2+kg0^1@2$4+1@2$5+8^1").
Definition max_count : ltac2:(zQ "10!h9>1c$0$0") := ltac2:(zQ "40!h9!hl1!hle!pd\1c$0@2$3+2@1$2@1$1^1").

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rz_log : ltac2:(zQ "10!h9>1n$0$0") := ltac2:(zQ "30!rb!h9!s2\1n$1M0\0$0$1@2$2^1+j0ZM0\0$0$1@2$2^1+m0+1M0\0$0$1@2$2^1+hs0+2M0\0$0$1@2$2^1+vo0+3M0\0$0$1@2$2^1+jvg0+4M0\0$0$1@2$2^1+nug0+5M0\0$0$1@2$2^1+vsg0+6+7").
Definition rz_size : ltac2:(zQ "10!h9>1n$0$0") := ltac2:(zQ "70!h9!hn0!ho1!hp2!hk5!hkb!hi0\1n$0@2$6+h0@2$5@2$4@1$3^1$2$1").

Record req := mkReq {
  rq_n        : Z;     (* [comment removed for export] *)
  rq_size     : Z;     (* [comment removed for export] *)
  rq_rz       : Z;     (* [comment removed for export] *)
  rq_rounded  : Z;     (* [comment removed for export] *)
  rq_needed   : Z;     (* [comment removed for export] *)
  rq_primary  : bool   (* [comment removed for export] *)
}.

Definition compute_req : ltac2:(zQ "20!h9!hpb>1n$0$1") := ltac2:(zQ "a0!h9!rb!p1!hq1!hqc!hr4!hrf!hh4!s2!hk5\1n$0=5size'$0M1\0$1$0@2$7^1Z+1^1=2rz$0@1$6^2=7rounded$0@2$5@2$9^3+8+8=7needed0$0@2$2^1^2=4prim$1@2$8^1$3=6needed$0M1\4prim$1$0^1^2@2$2^2^4@6$4^7^6^5^4^1^2").

(* [comment removed for export] *)
Definition size_too_big : ltac2:(zQ "20!rb!hpb>1r$1$0") := ltac2:(zQ "70!hs9!hj6!sf!hpb!hte!hu5!hv1\1r$3@2$2@2$2@2$1$0@1$4^1@2$1$0@1$5^1@2$1$0@1$6^1").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record region := mkRegion {
  rg_mapped_user       : Z;
  rg_allocated_user    : Z;
  rg_num_freed         : Z;            (* [comment removed for export] *)
  rg_free_array        : list Z;       (* [comment removed for export] *)
  rg_mapped_free_array : Z
}.
Definition region0 : ltac2:(zQ "10!hvb$0") := ltac2:(zQ "30!ig4!h9!iga@5$2ZZZ@1$0$1Z").

(* [comment removed for export] *)
Record pclass := mkPC { pc_count : Z; pc_chunks : list Z (* [comment removed for export] *) }.
Definition pclass0 : ltac2:(zQ "10!ih5$0") := ltac2:(zQ "30!ig4!h9!ihe@2$2Z@1$0$1").

(* [comment removed for export] *)
Record schunk := mkSC { sc_map_beg : Z; sc_map_size : Z; sc_size : Z }.

(* [comment removed for export] *)
Inductive cstate := CAllocated | CQuarantine.
Record chunk := mkChunk {
  ch_alloc_beg : Z;      (* [comment removed for export] *)
  ch_user_beg  : Z;      (* [comment removed for export] *)
  ch_used      : Z;      (* [comment removed for export] *)
  ch_rz        : Z;
  ch_class     : Z;      (* [comment removed for export] *)
  ch_state     : cstate
}.
Definition ch_primary : ltac2:(zQ "20!rb!ii5>1c$1$0") := ltac2:(zQ "40!iid!ij4!ii5!hh4\1c$2@1$0@2$3@1$1^1Z").
Definition ch_chunk_beg : ltac2:(zQ "20!h9!ii5>1c$1$0") := ltac2:(zQ "40!ijf!ii5!ikd!o5\1c$1@2$3@1$0^1$2").

(* [comment removed for export] *)
Record qbatch := mkQB { qb_addr : Z; qb_size : Z; qb_count : Z; qb_chunks : list Z (* [comment removed for export] *) }.
(* [comment removed for export] *)
Record qcache := mkQC { qc_list : list qbatch; qc_bytes : Z }.
Definition qcache0 : ltac2:(zQ "10!im1$0") := ltac2:(zQ "30!ig4!ima!in6@2$1@1$0$2Z").

(* [comment removed for export] *)
Inductive mkind :=
  | MkPrimaryReservation          (* [comment removed for export] *)
  | MkRegionInfo                  (* [comment removed for export] *)
  | MkUserMap (cls : Z)           (* [comment removed for export] *)
  | MkFreeArrayMap (cls : Z)      (* [comment removed for export] *)
  | MkPtrArrayReservation         (* [comment removed for export] *)
  | MkPtrArrayCommit              (* [comment removed for export] *)
  | MkSecondary                   (* [comment removed for export] *)
  | MkShadowRemap.                (* [comment removed for export] *)
Record mapping := mkMap { mp_base : Z; mp_size : Z; mp_kind : mkind; mp_prot : Z; mp_lazy : bool }.

(* [comment removed for export] *)
Inductive effect :=
  | EMmap (hint len prot flags ret : Z)     (* [comment removed for export] *)
  | EMunmap (addr len : Z)                  (* [comment removed for export] *)
  | EPoison (addr size val : Z)             (* [comment removed for export] *)
  | EShadow1 (app_addr val : Z)             (* [comment removed for export] *)
  | EFill (addr n byte : Z)                 (* [comment removed for export] *)
  | EStore64 (addr val : Z)                 (* [comment removed for export] *)
  | EInternalAllocInit.                     (* [comment removed for export] *)

Record astate := mkState {
  as_space_beg     : Z;                 (* [comment removed for export] *)
  as_ptr_array     : Z;                 (* [comment removed for export] *)
  as_regions       : list region;       (* [comment removed for export] *)
  as_cache_inited  : bool;              (* [comment removed for export] *)
  as_cache         : list pclass;       (* [comment removed for export] *)
  as_n_reserved    : Z;                 (* [comment removed for export] *)
  as_sec           : list schunk;       (* [comment removed for export] *)
  as_chunks        : PositiveMap.t chunk; (* [comment removed for export] *)
  as_tq            : qcache;            (* [comment removed for export] *)
  as_gq            : qcache;            (* [comment removed for export] *)
  as_internal_init : bool;              (* [comment removed for export] *)
  as_maps          : list mapping;      (* [comment removed for export] *)
  as_shadow        : list (Z * Z * Z);  (* [comment removed for export] *)
  as_env           : list Z;            (* [comment removed for export] *)
  as_track_shadow  : bool;              (* [comment removed for export] *)
  as_qmax          : Z;                 (* [comment removed for export] *)
  as_qmin          : Z;                 (* [comment removed for export] *)
  as_qcache        : Z                  (* [comment removed for export] *)
     (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition get_region : ltac2:(zQ "30!h9!inf!hvb>2st$1>1c$0$2") := ltac2:(zQ "70!h9!io8!inf!hvb!ip5!ipf!iq6\2st$2\1c$0@4$6$3@1$1^2@1$5^1$4").
Definition set_region : ltac2:(zQ "30!inf!h9!hvb>2st$0>1c$1>1r$2$0") := ltac2:(zQ "h80!hvb!h9!iqd!ir8!isa!it6!itf!iu7!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jm8!jn0!inf!jo2!joc!ipf\2st$h4\1c$1\1r$0@h2$h5@1$h1^3@1$a^3@4$h6$0@1$e^3@1$h7^2^1@1$3^3@1$2^3@1$9^3@1$f^3@1$4^3@1$h2^3@1$6^3@1$7^3@1$8^3@1$h0^3@1$5^3@1$h3^3@1$c^3@1$d^3@1$b^3").
Definition get_pc : ltac2:(zQ "30!h9!inf!ih5>2st$1>1c$0$2") := ltac2:(zQ "70!h9!iqd!inf!ih5!jp6!ipf!iq6\2st$2\1c$0@4$6$3@1$1^2@1$5^1$4").
Definition set_pc : ltac2:(zQ "30!inf!h9!ih5>2st$0>1c$1>1p$2$0") := ltac2:(zQ "h80!ih5!h9!iqd!ir8!isa!it6!itf!iu7!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jm8!jn0!inf!jo2!joc!ipf\2st$h4\1c$1\1p$0@h2$h5@1$h1^3@1$a^3@1$e^3@1$3^3@4$h6$0@1$2^3@1$h7^2^1@1$9^3@1$f^3@1$4^3@1$h2^3@1$6^3@1$7^3@1$8^3@1$h0^3@1$5^3@1$h3^3@1$c^3@1$d^3@1$b^3").
Definition set_cache_inited : ltac2:(zQ "10!inf>2st$0$0") := ltac2:(zQ "h40!jq0!iqd!isa!it6!itf!iu7!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jm8!jn0!inf!jo2\2st$h2@h2$h3@1$f^1@1$8^1@1$c^1$0@1$1^1@1$7^1@1$d^1@1$2^1@1$h0^1@1$4^1@1$5^1@1$6^1@1$e^1@1$3^1@1$h1^1@1$a^1@1$b^1@1$9^1").
Definition set_sec : ltac2:(zQ "40!inf!jq7!h9!jqe>2st$0>4nres$2>1s@1$1$3$0") := ltac2:(zQ "h50!jq7!h9!iqd!ir8!isa!it6!itf!iu7!ivb!jh5!ji4!jj0!jja!io8!jkd!jl9!jm8!jn0!inf!jo2!jqe\2st$h2\4nres$1\1s@1$0$h4@h2$h3@1$f^3@1$9^3@1$d^3@1$3^3@1$2^3^2^1@1$4^3@1$h0^3@1$6^3@1$7^3@1$8^3@1$e^3@1$5^3@1$h1^3@1$b^3@1$c^3@1$a^3").
Definition set_chunks : ltac2:(zQ "30!inf!ii5!jte>2st$0>1l@1$2$1$0") := ltac2:(zQ "h50!iqd!ir8!it6!itf!iu7!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jm8!jn0!inf!ii5!jo2!jte\2st$h1\1l@1$h4$h2@h2$h3@1$e^2@1$7^2@1$b^2@1$1^2@1$0^2@1$6^2@1$c^2^1@1$f^2@1$3^2@1$4^2@1$5^2@1$d^2@1$2^2@1$h0^2@1$9^2@1$a^2@1$8^2").
Definition set_tq : ltac2:(zQ "20!inf!im1>2st$0>1q$1$0") := ltac2:(zQ "h40!iqd!ir8!isa!it6!itf!iu7!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jn0!inf!jo2!im1\2st$h1\1q$h3@h2$h2@1$f^2@1$8^2@1$c^2@1$1^2@1$0^2@1$7^2@1$d^2@1$2^2^1@1$4^2@1$5^2@1$6^2@1$e^2@1$3^2@1$h0^2@1$a^2@1$b^2@1$9^2").
Definition set_gq : ltac2:(zQ "20!inf!im1>2st$0>1q$1$0") := ltac2:(zQ "h40!iqd!ir8!isa!it6!iu7!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jm8!jn0!inf!jo2!im1\2st$h1\1q$h3@h2$h2@1$e^2@1$7^2@1$b^2@1$1^2@1$0^2@1$6^2@1$c^2@1$2^2@1$f^2^1@1$4^2@1$5^2@1$d^2@1$3^2@1$h0^2@1$9^2@1$a^2@1$8^2").
Definition set_internal_init : ltac2:(zQ "10!inf>2st$0$0") := ltac2:(zQ "h40!jq0!iqd!ir8!isa!it6!itf!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jm8!jn0!inf!jo2\2st$h2@h2$h3@1$f^1@1$8^1@1$c^1@1$2^1@1$1^1@1$7^1@1$d^1@1$3^1@1$h0^1@1$5^1$0@1$6^1@1$e^1@1$4^1@1$h1^1@1$a^1@1$b^1@1$9^1").
Definition add_map : ltac2:(zQ "20!inf!ju3>2st$0>1m$1$0") := ltac2:(zQ "h60!ju3!jud!iqd!ir8!isa!it6!itf!iu7!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jm8!jn0!inf!jo2\2st$h4\1m$0@h2$h5@1$h1^2@1$a^2@1$e^2@1$3^2@1$2^2@1$9^2@1$f^2@1$4^2@1$h2^2@1$6^2@1$7^2@3$1$0^1@1$8^2@1$h0^2@1$5^2@1$h3^2@1$c^2@1$d^2@1$b^2").
Definition remove_map : ltac2:(zQ "20!inf!h9>2st$0>4base$1$0") := ltac2:(zQ "ha0!ju3!iid!h9!iqd!ir8!isa!it6!itf!iu7!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jm8!jn0!inf!jo2!jv4!kh1!hh4\2st$h5\4base$2@h2$h6@1$h2^2@1$b^2@1$f^2@1$4^2@1$3^2@1$a^2@1$h0^2@1$5^2@1$h3^2@1$7^2@1$8^2@3$h8$0\1m$0@1$1@2$h9@1$h7^1^2@1$9^2@1$h1^2@1$6^2@1$h4^2@1$d^2@1$e^2@1$c^2").
Definition paint : ltac2:(zQ "20!h9!inf>2st$1>2lo$0>2hi$0>1v$0$1") := ltac2:(zQ "hb0!h9!khb!rb!ki2!jn0!jud!jq7!ig4!iqd!ir8!isa!it6!itf!iu7!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jm8!inf!jo2\2st$h9\2lo$0\2hi$0\1v$0@h2$ha@1$h7^4@1$h0^4@1$h4^4@1$9^4@1$8^4@1$f^4@1$h5^4@1$a^4@1$h8^4@1$c^4@1$d^4@1$e^4M2\0$2@1$6@2$1@2$1$0$0$0@1$4^4@3$5@2$1@2$1$0$0$0@4$3@2$1$0$0$0@4$3$0$0^3^2^1@1$h6^4@1$7@2$1@2$1$0$0$0@1$b^4@1$4^4@1$h2^4@1$h3^4@1$h1^4").
Definition pop_env : ltac2:(zQ "30!inf!khb!h9>2st$0@2$1$2$0") := ltac2:(zQ "h80!h9!inf!jq7!ki2!khb!iqd!ir8!isa!it6!itf!iu7!ivb!jg5!jh5!ji4!jj0!jja!io8!jk4!jkd!jl9!jm8!jn0!jo2\2st$1M2\1x@1$2$0@2$4$0$1@1$8^1@4$3$0$1Z^1\1k$0\1r@1$2$0@4$3$0$1^2@h2$h7@1$h4^3@1$d^3@1$h1^3@1$6^3@1$5^3@1$c^3@1$h2^3@1$7^3@1$h5^3@1$9^3@1$a^3@1$b^3@1$h3^3^1@1$h6^3@1$f^3@1$h0^3@1$e^3").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ckey : ltac2:(zQ "20!h9!ki9>4user$0$1") := ltac2:(zQ "20!h9!kj3\4user$0@1$1^1").
Definition find_chunk : ltac2:(zQ "40!ii5!kjc!h9!jte>1m@1$3$0>4user$2@1$1$0") := ltac2:(zQ "90!ii5!rb!kk5!kjc!h9!kkc!kl3!jte!s2\1m@1$7$0\4user$4M1\0$1@1$3$0@2$8^1Z@1$2$0@3$6$0@1$5^1^2").
Definition remove_chunk : ltac2:(zQ "30!ii5!jte!h9>1m@1$1$0>4user$2@1$1$0") := ltac2:(zQ "50!ii5!h9!kkc!klb!jte\1m@1$4$0\4user$1@3$3$0@1$2^1^2").
Definition upd_chunk : ltac2:(zQ "20!inf!ii5>2st$0>1c$1$0") := ltac2:(zQ "70!ii5!isa!inf!ijf!kkc!km5!kn2\2st$2\1c$0@2$5^2@4$6$0@1$4@1$3^1^1@1$1^2").
Definition chunk_list : ltac2:(zQ "30!jq7!inf!ii5>2st$1@1$0$2") := ltac2:(zQ "80!ii5!kn9!khb!ko0!kpd!isa!inf!kq4\2st$6@4$4@2$2$1$0$0@2$3$1$0@2$7$0@1$5^1").

Definition region_beg : ltac2:(zQ "20!h9!inf>2st$1>1c$0$0") := ltac2:(zQ "60!h9!jl9!inf!kr0!p1!hi0\2st$2\1c$0@2$4@1$1^2@2$5^1$3").
Definition free_array_base : ltac2:(zQ "20!h9!inf>2st$1>1c$0$0") := ltac2:(zQ "50!h9!inf!ks1!kt5!p1\2st$1\1c$0@2$4@2$3^2^1$2").
Definition compact_to_addr : ltac2:(zQ "20!h9!inf>2st$1>1c$0>2cp$0$0") := ltac2:(zQ "60!h9!inf!ku2!kt5!p1!hi0\2st$1\1c$0\2cp$0@2$4@2$3^3^2@2$5^1$2").
Definition addr_to_compact : ltac2:(zQ "20!h9!inf>2st$1>1c$0>1a$0$0") := ltac2:(zQ "60!h9!inf!ku2!kt5!hjc!o5\2st$1\1c$0\1a$0@2$4@2$5^1@2$3^3^2$2").
Definition in_primary : ltac2:(zQ "30!rb!h9!inf>2st$2>1a$1$0") := ltac2:(zQ "80!jl9!s8!h9!inf!kv6!p1!s2!hj6\2st$3\1a$2@2$1@2$6@1$0^2^1@2$7^1@2$5@1$0^2$4").
Definition class_of_addr : ltac2:(zQ "20!h9!inf>2st$1>1a$0$0") := ltac2:(zQ "70!h9!jl9!inf!kr0!hi9!hjc!o5\2st$2\1a$0@2$4@2$5@2$6^1@1$1^2$3+hf").

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition poison_shadow : ltac2:(zQ "60!h9!inf!jq7!kjc!khb!lg3>2st$1>4addr$0>4size$0>3val$0@1$3@2$4$1@1$2$5") := ltac2:(zQ "he2!lg3!inf!jq7!rb!khb!h9!kjc!jud!iid!kk5!lgc!ig4!ki2!p1!o5!hh4!lh3!li4!lj0!hi9!hj6!lk0!lk8!ll2!lld!lm7!lo4!loc!hr4!s2&@4$c$1@1$2$0^2@3$7$0^1@1$b$0&@2$a@2$4$1@1$2$0~0\2st$1\4addr$5\4size$5\3val$5M3\0$3@1$6@2$4$1@1$2$0@1$8@2$f@2$h3^3+7Z@1$9@2$4$1@1$2$0M3\0$3@1$6@2$4$1@1$2$0@1$8@1$h0^3@1$9@2$4$1@1$2$0M3\0$3@1$6@2$4$1@1$2$0@1$8@2$f@2$h3^2+7Z@1$9@2$4$1@1$2$0M3\0$3@1$6@2$4$1@1$2$0@1$8@1$h0@2$e@2$d^3^2+8@1$9@2$4$1@1$2$0=ashadow_beg$5@1$h2^3=ashadow_end$5@2$d@1$h2@2$e@2$d^4^3+8+1=3len$5@2$e^1^2=3st'$1M3\0$3$1@2$h4Z^5@4$ha^7^6@2$d^6^5^4^7=2ev$0@3$h6^7^6^5M3\0$3@1$6@2$4$1@1$2$0@1$8@2$f^6Z~1M3\0$3@1$6@2$4$1@1$2$0@2$h4^3$h9~1=8page_beg$5@2$hc^5$h1=8page_end$5@2$hb^5$h1M3\0$3@1$6@2$4$1@1$2$0@2$hd^1^2@2$a@2$4$1@1$2$0@4$c$1@1$2$0^4@3$7$0^3@1$b$0@2$a@2$4$1@1$2$0@4$c$1@1$2$0^4@3$7$0^3@3$7$0@5$h5^2@2$e^1^2$h8$h7^2@1$b$0").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ensure_cache_inited : ltac2:(zQ "10!inf>2st$0$0") := ltac2:(zQ "40!rb!inf!ir8!lp9\2st$1M0\0$0$1@1$2^1^1@1$3^1").

(* [comment removed for export] *)
Definition map_fixed : ltac2:(zQ "60!h9!inf!jq7!khb!lg3!lqd>2st$1>4addr$0>4size$0>1k$5@2$3$1@1$2$4") := ltac2:(zQ "e0!lg3!h9!lld!inf!jud!lr5!jq7!ig4!ki2!lk0!lrd!ls7!lt1!lqd\2st$3\4addr$1\4size$1\1k$d@4$8$3@1$6$0@2$b^4@5$c^3^2^1$2$5@3$4$0@5$9^3^2$2$a^3@1$7$0").

(* [comment removed for export] *)
Definition ensure_free_array_space : ltac2:(zQ "60!h9!inf!jq7!kjc!khb!lg3>2st$1>1c$0>9num_freed$0@1$3@2$4$1@1$2$5") := ltac2:(zQ "i21!lg3!inf!jq7!khb!kjc!h9!rb!lt9!kk5!lgc!ki2!hvb!lv1!ig4!lv7!mg8!mha!mi7!mk4!ml9!mma!iga!mn6!mo6!mpb!mqb!mrc!hr4!msb!p1!s2!hj6!pd!o5&\1p@2$3$1@1$2$0@1$4@2$3$1@1$2$0\2st$1\1c$5\9num_freed$5=1r$b@2$h0^3^2=6needed$5@2$i0^2+4M6\0$6@1$4@2$3$1@1$2$0@2$he^1@1$7^2@2$9@2$3$1@1$2$0@4$a$1@1$2$0^5@1$d$0=anew_mapped$5@2$hb^1$h2M6\0$6@1$4@2$3$1@1$2$0@2$hf$h3^1@1$8@2$3$1@1$2$0=7cur_end$5@2$hd@2$f^6^5@1$7^3=2sz$5@2$i1^2@1$7^4M3~0@4$h4^8^2^1@1$e^7\3st1$1\3ev1@1$2$0M4\1x@1$4@2$3$1@1$2$0@1$4@2$3$1@1$2$0@4$h6^2^4^3$h1\1p@2$3$1@1$2$0M3~0^1\3st2$1\3ev2@1$2$0=2r'$b@5$h5@1$h9^a@1$h7^a@1$ha^a@1$h8^a^8@2$9@2$3$1@1$2$0@4$a$1@1$2$0@3$hc^3^d^1@3$c$0^5^2@1$8@2$3$1@1$2$0").

(* [comment removed for export] *)
Fixpoint carve_asc (base size : Z) (i : Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => Z.shiftr (base + i * size) kCompactPtrScale :: carve_asc base size (i + 1) k'
  end.

(* [comment removed for export] *)
Definition populate_free_array : ltac2:(zQ "60!h9!inf!jq7!kjc!khb!lg3>2st$1>1c$0>9requested$0@1$3@2$4$1@1$2$5") := ltac2:(zQ "i72!khb!inf!lg3!jq7!hvb!kjc!h9!mqb!p1!rb!mo6!kk5!ki2!lgc!lv1!mha!iga!mpb!lt9!mrc!msb!hj6!pd!o5!ig4!mt8!mu4!hl1!mv0!mi7!ks1!ngb!mma!mn6!kt5!hr4!p7!s2!hgb&\0$9@1$5@2$0@2$0$1$4@1$3$2&\1p@2$0$1@1$3$2@1$5@2$0@2$0$1$4@1$3$2\2st$1\1c$6\9requested$6=1r$4@2$f^3^2=4size$6@1$hb^3=h0total_user_bytes$6@2$8@1$a^2@2$h6^3^1=5step1@1$5@2$0@2$0$1$4@1$3$2M9~0@2$i5^1@1$7^3@2$d@2$0@2$0$1$4@1$3$2@4$c@2$0$1$4@1$3$2@4$c$1$4^6^3@1$h8$2=duser_map_size$6@2$i3@2$h7^1@1$7^3$hfM9~0@2$h5$he@2$8@2$8@1$7^4Z^1@1$b@2$0@2$0$1$4@1$3$2=3beg$6@2$8@2$i2^7^6@1$7^4M0~1@4$i0^8^1^2@1$h9^7\3st1$1\3ev1@1$3$2M5\1x@1$5@2$0$1@1$3$2@1$5@2$0@2$0$1$4@1$3$2@4$i1^2^3^4$hd\1p@2$0$1@1$3$2M0~1^1\3st2$1\3ev2@1$3$2=2r'$4@5$h0@2$8@1$7^a^7@1$a^a@1$h3^a@1$h1^a@1$h2^a@2$d@2$0@2$0$1$4@1$3$2@4$c@2$0$1$4@1$3$2@4$c$1$4@3$h4^3^d^1^1@3$e$2^5^2@1$b@2$0@2$0$1$4@1$3$2M5\5step1@1$5@2$0@2$0$1$4@1$3$2@1$5@2$0$1@1$3$2^1\1p@2$0@2$0$1$4@1$3$2M0\1p@2$0@2$0$1$4@1$3$2@1$5@2$0$1@1$3$2^1\2p0@2$0$1$4\3ev1@1$3$2M0\2p0@2$0$1$4@1$5@2$0$1@1$3$2^2\3st1$1\2r1$4=anew_chunks$6@2$i4@2$h7@1$7^1@1$a^1^8=btotal_freed$6@2$8@1$h3^2^1M5\1x@1$5@2$0$1@1$3$2@1$5@2$0$1@1$3$2@3$hc^4^d^1\1p@2$0$1@1$3$2M0\1p@2$0$1@1$3$2@1$5@2$0$1@1$3$2^1\3st2$1\3ev2@1$3$2=2r2$4@2$f^2^h0=3seg@1$3$6@4$ha@1$a^1^eZ@1$i6^6=2r3$4@5$h0@1$7^2@2$8@1$a^2@2$h6^7^f^6@3$e$6^1@1$h1^2@1$h2^2M9\0$9@1$5@2$0$1@1$3$2@2$h5@1$7^1@1$a^1@1$b@2$0$1@1$3$2@2$d@2$0$1@1$3$2@4$c$1@1$3$2@3$h4^5^h3^1@3$e$2^b^4@1$b@2$0$1@1$3$2@1$b@2$0$1@1$3$2").

(* [comment removed for export] *)
Definition get_from_allocator : ltac2:(zQ "60!h9!jq7!khb!inf!kjc!lg3>2st$3>1c$0>1n$0@1$4@2$2@2$2$3@1$1$0@1$1$5") := ltac2:(zQ "hb1!jq7!khb!inf!lg3!kjc!h9!rb!ki2!mrc!kk5!lgc!mha!hvb!mpb!hj6!o5!hg5!ig4!nha!ni4!iga!nid!mo6!lt9!mqb!msb!hgb&@1$4@2$1@2$1$2@1$0$5@1$0$3\2st$2\1c$5\1n$5=1r$c@2$b^3^2=4step@1$4@2$1$2@1$0$3M6\0$6@1$4@2$1$2@1$0$3@2$e@1$8^1^2M4\1x@1$4@2$1$2@1$0$3@1$4@2$1$2@1$0$3@3$h5^4^3@2$f^2@1$8^1\1p@2$1$2@1$0$3M1\1p@2$1$2@1$0$3@1$4@2$1$2@1$0$3^1\3st1$2\3ev1@1$0$3M6\0$6@1$4@2$1$2@1$0$3@2$e@1$8@2$b^2^6^5@1$9@2$1$2@1$0$3@2$a@2$1$2@1$0$3@4$7$2@1$0$3^2^1@1$9@2$1$2@1$0$3@2$a@2$1$2@1$0$3@4$7$2@1$0$3^4@1$h1$3M4\4step@1$4@2$1$2@1$0$3~0^1\1p@2$1$2@1$0$3M1\1p@2$1$2@1$0$3~0^1\3st1$2\3ev1@1$0$3=2r1$c@2$b^2^7=1k$h0@1$ha^7=5taken@1$0$5@3$h2$5^1@1$d^2=2r2$c@5$h4@1$h8^3@1$h6^3@2$f@1$8^3^9@3$h3$5^2@1$d^3@1$h7^3@2$a@2$1@2$1$2@1$0$5@1$0$3@4$7@2$1$2@1$0$5@1$0$3@4$7$2@1$0$5@3$h9^6^b^1^2^5@1$9@2$1@2$1$2@1$0$5@1$0$3").

(* [comment removed for export] *)
Definition cache_alloc : ltac2:(zQ "60!khb!h9!inf!jq7!kjc!lg3>2st$2>1c$1@1$4@2$0@2$0$2$1@1$3$5") := ltac2:(zQ "hb0!khb!inf!jq7!lg3!h9!ih5!kjc!ki2!kk5!rb!lgc!ihe!nk4!hh4!ig4!sf!nkf!nm1!nn8!noe!np7!nq5!nr1!nrd!p7!s2!o5\2st$1\1c$4M9\0$9@1$6@2$0@2$0$1$4@1$2$3@2$f@2$d^1Z@2$h9$h4^1@1$8@2$0@2$0$1$4@1$2$3=2pc$5@2$h3^2^1=4step@1$6@2$0@2$0$1$5@1$2$3M9\0$9@1$6@2$0@2$0$1$5@1$2$3@2$d@1$c^1Z=3st1$1@1$h1^3=1n$4@2$h8@1$h5^3+2M6\1x@1$6@2$0@2$0$1@1$2$4@1$2$3@1$6@2$0@2$0$1$5@1$2$3@3$h2^2^4^1\1p@2$0@2$0$1@1$2$4@1$2$3M0\1p@2$0@2$0$1@1$2$4@1$2$3@1$6@2$0@2$0$1$5@1$2$3^1\2p0@2$0$1@1$2$4\2ev@1$2$3M0\2p0@2$0$1@1$2$4@1$6@2$0@2$0$1$5@1$2$3^2\3st2$1\5taken@1$2$4@2$a@2$0@2$0$1$5@1$2$3@4$7@2$0$1$5@1$2$3@4$7$1$5^2@2$b^6^1^3@1$8@2$0@2$0$1$5@1$2$3@2$a@2$0@2$0$1$5@1$2$3@4$7@2$0$1$5@1$2$3@4$7$1$5^3^1@1$e$3M6\4step@1$6@2$0@2$0$1$5@1$2$3@1$6@2$0@2$0$1$4@1$2$3^1\1p@2$0@2$0$1$5@1$2$3M0\1p@2$0@2$0$1$5@1$2$3@1$6@2$0@2$0$1$4@1$2$3^1\2p0@2$0$1$5\2ev@1$2$3M0\2p0@2$0$1$5@1$6@2$0@2$0$1$4@1$2$3^2\3st1$1\3pc1$5M2\1x@1$2$4@1$6@2$0@2$0$1$4@1$2$3@1$h6^1@1$8@2$0@2$0$1$4@1$2$3\2cp$4\4rest@1$2$4=3st2$1@3$h7^4^a@2$b@2$ha@1$c^3+1^1@2$a@2$0@2$0$1$4@1$2$3@4$7@2$0$1$4@1$2$3@4$7$1$4^1@3$h0^1^b^3^6@1$8@2$0@2$0$1$4@1$2$3").

(* [comment removed for export] *)
Definition return_to_allocator : ltac2:(zQ "60!h9!jq7!inf!kjc!khb!lg3>2st$2>1c$0>1n$0>6cps_tf@1$1$0@1$3@2$4$2@1$1$5") := ltac2:(zQ "h50!jq7!inf!lg3!khb!h9!kjc!hvb!mha!kk5!lgc!lv1!ki2!mv0!iga!mo6!mpb!lt9!mqb!mrc!msb!p1\2st$1\1c$4\1n$4\6cps_tf@1$0$4=1r$6@2$7^4^3=7new_num$4@2$h4@1$h2^1^3M5\1x@1$5@2$3$1@1$0$2@1$5@2$3$1@1$0$2@3$c^6^5^1\1p@2$3$1@1$0$2M3\1p@2$3$1@1$0$2@1$5@2$3$1@1$0$2^1\3st1$1\2ev@1$0$2=2r1$6@2$7^2^8=2r2$6@5$d@1$h1^1@1$e^1^5@3$a$4^7@1$f^1@1$h0^1@2$9@2$3$1@1$0$2@4$b$1@1$0$2@3$h3^4^a^1^3@1$8@2$3$1@1$0$2").

(* [comment removed for export] *)
Definition cache_dealloc : ltac2:(zQ "60!h9!inf!jq7!kjc!khb!lg3>2st$1>1c$0>1p$0@1$3@2$4$1@1$2$5") := ltac2:(zQ "i21!khb!inf!jq7!lg3!ih5!kjc!h9!rb!ki2!kk5!nk4!lgc!nr1!nq5!ihe!nrd!hh4!jud!hg5!ig4!sf!nha!ni4!ns6!nm1!noe!np7!nt8!p1!p7!s2!hj6!o5!hgb&\0$7@1$5@2$0@2$0$1$4@1$2$3\2st$1\1c$6\1p$6M7\0$7@1$5@2$0$1@1$2$3@2$h4@2$h0^2Z@2$he$ha^2@1$9@2$0$1@1$2$3=3st0$1@1$h8^3=2pc$4@2$h9^1^3=4step@1$5@2$0@2$0$1$4@1$2$3M7~0@2$h0@1$a^1@1$d^4=3cnt$6@2$hd@1$d^4+2M7~0@2$hf@1$a^2^1@1$9@2$0@2$0$1$4@1$2$3=1k$h2@1$i1^1=3ret@1$2$6@3$h5$6^1@1$c^3=4keep@1$2$6@3$h6$6^2@1$c^4=3pck$4@2$e@2$i0@1$a^5^4^1M5\1x@1$5@2$0$1@1$2$3@1$5@2$0@2$0$1$4@1$2$3@4$hb@3$f^7^9^1^9^5^3\2p0@2$0$1@1$2$3M0\2p0@2$0$1@1$2$3@1$5@2$0@2$0$1$4@1$2$3^1\3st1$1\2ev@1$2$3@2$b@2$0@2$0$1$4@1$2$3@4$8@2$0$1$4@1$2$3@4$8$1$4^2^4^1@1$9@2$0@2$0$1$4@1$2$3@2$b@2$0@2$0$1$4@1$2$3@4$8@2$0$1$4@1$2$3@4$8$1$4^2^1@1$h3$3M5\4step@1$5@2$0@2$0$1$4@1$2$3@1$5@2$0$1@1$2$3^1\2p0@2$0@2$0$1$4@1$2$3M0\2p0@2$0@2$0$1$4@1$2$3@1$5@2$0$1@1$2$3^1\2p1@2$0$1$4\2ev@1$2$3M0\2p1@2$0$1$4@1$5@2$0$1@1$2$3^2\3st1$1\3pc1$4=3pc2$4@2$e@2$hc@1$a^1+1@3$h1$6@3$h7^2^a^9@1$c^1@2$b@2$0$1@1$2$3@4$8$1@1$2$3@3$f^3^b^1^4@1$9@2$0$1@1$2$3").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition large_allocate (st : astate) (needed : Z) (kaddr : Z) : option (astate * Z * list effect) :=
  let map_size := round_up needed kPageSize + kPageSize in
  if map_size <? needed then None else
  let map_beg := kaddr in
  if negb (Z.land map_beg (kPageSize - 1) =? 0) then None else              (* [comment removed for export] *)
  let ev0 := [EMmap 0 map_size PROT_RW MAP_PA map_beg] in
  let st0 := add_map st (mkMap map_beg map_size MkSecondary PROT_RW false) in
  let map_end := map_beg + map_size in
  let res := map_beg + kPageSize in
  (* [comment removed for export] *)
  match poison_shadow st0 map_beg (round_up res 8 - map_beg) kAsanHeapLeftRedzoneMagic with
  | None => None
  | Some (st1, ev1) =>
    let tail := round_down (res + needed) 8 in
    match poison_shadow st1 tail (map_end - tail) kAsanHeapLeftRedzoneMagic with
    | None => None
    | Some (st2, ev2) =>
      if map_end <? res + needed then None else                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      let n := zlen (as_sec st2) in
      if kMaxNumChunks <=? n then None else
      let '(st3, nres, ev3) :=
        if n =? as_n_reserved st2 then
          let (st', ev') := map_fixed st2 (as_ptr_array st2 + as_n_reserved st2 * 8) (kChunksBlockCount * 8) MkPtrArrayCommit in
          (st', as_n_reserved st2 + kChunksBlockCount, ev')
        else (st2, as_n_reserved st2, []) in
      let st4 := set_sec st3 nres (as_sec st3 ++ [mkSC map_beg map_size needed]) in
      Some (st4, res, ev0 ++ ev1 ++ ev2 ++ ev3)
    end
  end.

(* [comment removed for export] *)
Fixpoint nearest_le (l : list schunk) (m : Z) (best : option schunk) : option schunk :=
  match l with
  | [] => best
  | h :: r =>
      if m <? sc_map_beg h then nearest_le r m best
      else match best with
           | None => nearest_le r m (Some h)
           | Some b => if m - sc_map_beg h <? m - sc_map_beg b then nearest_le r m (Some h) else nearest_le r m best
           end
  end.
Definition large_get_block_begin : ltac2:(zQ "30!h9!kjc!inf>2st$2>1m$0@1$1$0") := ltac2:(zQ "e0!h9!kjc!lgc!jqe!rb!nuf!p1!kk5!jk4!inf!li4!nvc!og9!s2\2st$9\1m$0M1\1x@1$1$3@1$1$0@3$b@1$8^2^1@1$7$3\1h$3M4\0$4@1$1$0@2$d@2$6@1$5^1@1$c^1^2@2$2$0Z@2$2$0@2$6@1$5^1$a@2$2$0Z").

Fixpoint find_sec_idx (l : list schunk) (map_beg : Z) (i : nat) : option nat :=
  match l with [] => None | h :: r => if sc_map_beg h =? map_beg then Some i else find_sec_idx r map_beg (S i) end.

(* [comment removed for export] *)
Definition large_deallocate : ltac2:(zQ "60!inf!jq7!kjc!khb!h9!lg3>2st$0>1p$4@1$2@2$3$0@1$1$5") := ltac2:(zQ "i50!inf!lg3!jq7!khb!kjc!jqe!jk4!kk5!rb!hg5!og9!iid!oi9!h9!lh3!li4!oj0!iq6!o5!lgc!s8!lv1!jud!oj7!ig4!ki2!nha!ok0!jg5!oka!mn6!ol9!om6!joc!p1!hh4!hi9\2st$0\1p$dM8\0$8@1$4@2$3$0@1$2$1@1$b@2$i3@2$i4^1@2$h2$f+1Z@1$7@2$3$0@1$2$1=7map_beg$d@2$h2^1$fM4\1x@1$4$9@1$4@2$3$0@1$2$1@3$hd@1$6^3^1N0\3idx$9=1h$5@4$h1$5@1$6^4^1@3$h0ZZZ=1n$9@2$h7$5@1$6^5=4last$5@4$h1$5@1$6^6@2$c^1N1@3$h0ZZZ=2l1@1$2$5@3$ha$5@2$c^2N1@4$i1$5@1$6^7^4^1=3st1$0@3$i0^8@1$hc^8^1M4\1x@1$4@2$3$0@1$2$1@1$4@2$3$0@1$2$1@4$he^1^7@1$a^5Z\2p0@2$3$0@1$2$1M3\2p0@2$3$0@1$2$1@1$4@2$3$0@1$2$1^1\3st2$0\3ev2@1$2$1M8\0$8@1$4@2$3$0@1$2$1@1$b@2$h4@1$e^a@1$e@2$i2^a@1$a^8@1$7@2$3$0@1$2$1=3st3$0@2$hf^2^a@2$h3@2$3$0@1$2$1@4$h9$0@1$2$1^1@3$h5$1^2@3$h6$1@2$hb^b@1$a^9@1$h8$1@1$7@2$3$0@1$2$1@1$7@2$3$0@1$2$1").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition actually_allocated_size : ltac2:(zQ "30!h9!kjc!inf>2st$2>9allocated$0@1$1$0") := ltac2:(zQ "h40!h9!rb!kjc!kk5!li4!jqe!lgc!hh4!o5!iid!jk4!inf!on0!hl1!oo0!nvc!hr4!nuf!ood!hi9\2st$b\9allocated$0M1\0$1@1$2$0@2$e^2^1@2$6$0@1$d@2$c^2^1M1\0$1@1$2$0@1$9@2$7@2$h3^1@2$8$4+1Z@1$3$0M2\1x@1$2$5@1$2$0@3$f@1$a^2^1@1$3$5\1h$5M1\0$1@1$2$0@2$7@1$h1^1@2$8^2$4@2$6$0@2$h0@1$h2^1$4@1$3$0@1$3$0").

Definition am_malloc_k : ltac2:(zQ "60!h9!khb!inf!jq7!kjc!lg3>2st$2>1n$0>5kaddr$0@1$4@2$1@2$1$0$2@1$3$5") := ltac2:(zQ "j0b!khb!inf!lg3!jq7!h9!kjc!rb!kk5!ki2!lgc!hv1!p1!lv1!ig4!hj6!iid!o5!mn6!hi9!jud!mi7!ikd!op7!hh4!s8!opf!oqc!or4!orf!lh3!ota!ii5!ou8!ov3!pg1!ph3!hq1!pi9!pja!lo4!hpb!hr4!hu5!pk4!pl1!pm0!pmc!hkb&\0$6@1$5@2$0@2$0$4$1@1$3$2&@2$0@2$0@2$0$1$4$4@1$3$2&@1$5~1&\1x@1$5@2$0@2$0$1$4@1$3$2~2&\1p@2$0@2$0$1$4@1$3$2~2&\2p0@2$0$1$4~2&@1$7~1&\1x@1$5@2$0$1@1$3$2@1$5@2$0$1@1$3$2&\1p@2$0$1@1$3$2@1$5@2$0$1@1$3$2&\1p@2$0$1@1$3$2@1$5@2$0@2$0$4$1@1$3$2&@2$9@2$0$1@1$3$2@4$8$1@1$3$2^3@1$d$2\2st$1\1n$4\5kaddr$4M6~0@2$e^2Z@1$7@2$0@2$0$4$1@1$3$2=1r$i8@1$i1^2M6~0@1$ic^1@1$7@2$0@2$0$4$1@1$3$2=6needed$4@1$ia^1=5alloc~2M6\0$6~2@2$e$i4^1M5~3@3$i5^5^1^3\1p@2$0@2$0$1$4@1$3$2M0~4^1\2p0@2$0$1$4\2ev@1$3$2M0~5^2\3st1$1\3res$4@2$9~1@4$8@2$0@2$0$1$4$4@1$3$2@4$8@2$0$1$4$4@4$8$1$4^2^1Z^3~6=1c$4@1$i0^1M5~3@2$he^6^1\1p@2$0@2$0$1$4@1$3$2M0~4^1\2p0@2$0$1$4\2ev@1$3$2M0~5^2\3st1$1\1a$4@2$9~1@4$8@2$0@2$0$1$4$4@1$3$2@4$8@2$0$1$4$4@4$8$1$4^2^1^6^3~6M5\5alloc~2@1$5@2$0@2$0$4$1@1$3$2^1\1p~1M0\1p~1@1$5@2$0@2$0$4$1@1$3$2^1\2p0@2$0@2$0$1$4$4\3ev1@1$3$2M0\2p0@2$0@2$0$1$4$4@1$5@2$0@2$0$4$1@1$3$2^2\2p1@2$0$1$4\3cls$4M0\2p1@2$0$1$4@1$5@2$0@2$0$4$1@1$3$2^2\3st1$1\9allocated$4=8user_beg$4@2$b^1@1$h6^a=8user_end$4@2$b^1@1$a^bM6~0@2$e@2$b^3^b^1@1$7@2$0@2$0$4$1@1$3$2=2ch$hf@6$i6^3^2@1$a^c@1$h6^c^5$h9=3st2$1@2$id^5^1=5do_rz$6@1$f@1$ib^e=6step13@1$5@2$0$1@1$3$2M6\5do_rz$6@1$5@2$0$1@1$3$2^1M5\1x@1$5$4@1$5@2$0$1@1$3$2@2$hc^2^6\3asz$4=8tail_beg$4@2$i9^5+8M5~7@4$h1^4^8@2$h0^7^8$h4\1p@2$0$1@1$3$2M0~8^1\3st3$1\2e3@1$3$2M5~7@4$h1^2^4@2$h0@2$b^b^5^4$h4\1p@2$0$1@1$3$2M0~8^1\3st4$1\2e4@1$3$2@2$9@2$0$1@1$3$2@4$8$1@1$3$2^2@3$c$2^4^1@1$7@2$0$1@1$3$2@1$7@2$0$1@1$3$2@1$7@2$0$1@1$3$2@2$9@2$0$1@1$3$2@4$8$1@1$3$2^2@1$d$2M5\6step13@1$5@2$0$1@1$3$2@1$5@2$0@2$0$4$1@1$3$2^1\1p@2$0$1@1$3$2M0~9^1\3st3$1\3ev3@1$3$2=2rd$4@2$h2@1$a^h3@1$ie+7=6step14@1$5@2$0$1@1$3$2M6\0$6@1$5@2$0$1@1$3$2@2$eZ^1@4$h1^3^a^1Z~aM5\6step14@1$5@2$0$1@1$3$2@1$5@2$0@2$0$4$1@1$3$2^1\1p@2$0$1@1$3$2M0~9^1\3st4$1\3ev4@1$3$2=1g$4@2$b^e^5=6step15@1$5@2$0$1@1$3$2M6\0$6@1$5@2$0$1@1$3$2@1$f@2$h7@1$a^h9^6M6\0$6@1$5@2$0$1@1$3$2@1$f@1$hd^1@1$7@2$0$1@1$3$2@2$9@2$0$1@1$3$2@4$8$1@1$3$2@4$i7^3^1@2$b^1+8@2$h2@1$a^h9+7@3$h3$2@2$hb^1@2$h2@1$a^h9+7@1$d$2~aM5\6step15@1$5@2$0$1@1$3$2@1$5@2$0@2$0$4$1@1$3$2^1\1p@2$0$1@1$3$2M0~9^1\3st5$1\3ev5@1$3$2=4fill@1$3$2@3$h3$2@3$ha^h3@2$if@1$a^hd$i3$i2@1$d$2M6~0@2$h8@1$f@2$h7@2$h0^h4$h5^h5@2$e@2$h0^h4$h5@2$b^h5+h0@1$7@2$0@2$0$4$1@1$3$2@2$9@2$0@2$0$4$1@1$3$2@4$8@2$0$4$1@1$3$2@4$8$4$1^h4^3@3$c$2^h9@3$c$2^c@3$c$2^7@3$c$2^2^1@1$7@2$0@2$0$4$1@1$3$2@1$7@2$0@2$0$4$1@1$3$2@1$7@2$0@2$0$4$1@1$3$2@1$7@2$0@2$0$4$1@1$3$2").

Definition am_malloc_full : ltac2:(zQ "60!khb!h9!inf!jq7!kjc!lg3>2st$2>1n$1@1$4@2$0@2$0$1$2@1$3$5") := ltac2:(zQ "c0!khb!h9!inf!rb!jq7!kjc!pn3!lg3!ov3!po1!hpb!pk4\2st$2\1n$1=1r$a@1$8^1M3\0$3@1$5@2$0@2$0$1$2@1$4$7@1$b^1@3$6^3^2ZM0\1p@2$0$1$2@1$5@2$0@2$0$1$2@1$4$7@1$9^3\1k$1\3st'$2@3$6^1^4^2").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cb_recycle : ltac2:(zQ "60!inf!jq7!kjc!khb!h9!lg3>2st$0>1m$4@1$2@2$3$0@1$1$5") := ltac2:(zQ "ia2!inf!lg3!jq7!khb!kjc!rb!kk5!h9!hh4!isa!ijf!p1!iid!pob!ii5!ppa!oo0!kt5!pq3!km5!p7!pd!lgc!lv1!ki2!pr2!ps2!psd!on0!hl1!pt7!mha!mi7!ikd!pu4!pv8!mn6!hvb!mqb!hr4!hj6!o5&\1x@1$4@2$3$0@1$2$1@1$4@2$3$0@1$2$1&\2p0@2$3$0@1$2$1@1$4@2$3$0@1$2$1\2st$0\1m$7M4\1x@1$4$e@1$4@2$3$0@1$2$1@2$he@1$9^2@2$b^1$i1\2ch$eMf\1x$f@1$4@2$3$0@1$2$1@1$ha^1@1$6@2$3$0@1$2$1M5\0$5@1$4@2$3$0@1$2$1@2$h0^3^2=1c$7@2$hc^3^2=4size$7@1$hd^1M5\0$5@1$4@2$3$0@1$2$1@2$8^2Z@1$6@2$3$0@1$2$1=3off$7@2$i9^4@2$h1^5^2=3beg$7@2$b@2$h1^6^3@2$h5@2$h4^1^2^2=1r$i5@2$hf^7^4M5\0$5@1$4@2$3$0@1$2$1@2$i8@1$i6^1@2$h5@2$b@2$h4^3^4+1^4@1$6@2$3$0@1$2$1=1p$7^2M5\0$5@1$4@2$3$0@1$2$1@1$c@2$8^1@1$d^7@1$6@2$3$0@1$2$1M4~0@4$i4^9@1$a^7@2$i7@1$hb^7+8$i0\2p0@2$3$0@1$2$1M3~1^1\3st1$0\3ev1@1$2$1=3st2$0@2$h3^2@2$h2@1$9^2@1$a^aM4~0@3$h9^1^a^5\2p0@2$3$0@1$2$1M3~1^1\3st3$0\3ev3@1$2$1@2$h6@2$3$0@1$2$1@4$h8$0@1$2$1^2@3$h7$1^5^1@1$6@2$3$0@1$2$1@1$6@2$3$0@1$2$1M4\1x@1$4$7@1$4@2$3$0@1$2$1@2$i3^3^2\1p$7M5\0$5@1$4@2$3$0@1$2$1@2$8^1Z@1$6@2$3$0@1$2$1M5\0$5@1$4@2$3$0@1$2$1@2$h0^4^1@1$6@2$3$0@1$2$1M5\0$5@1$4@2$3$0@1$2$1@1$c@2$8^1@1$d^2@1$6@2$3$0@1$2$1=3st1$0@2$h3^4@2$h2@1$9^4@1$a^2@2$i2^1^2@1$6@2$3$0@1$2$1@1$6@2$3$0@1$2$1").

(* [comment removed for export] *)
Fixpoint cb_recycle_list (st : astate) (ms : list Z) (racc : list effect) : option (astate * list effect) :=
  match ms with
  | [] => Some (st, racc)
  | m :: r => match cb_recycle st m with
              | None => None
              | Some (st1, ev) => cb_recycle_list st1 r (rev_append ev racc)
              end
  end.

(* [comment removed for export] *)
Fixpoint do_recycle (st : astate) (bs : list qbatch) (racc : list effect) : option (astate * list effect) :=
  match bs with
  | [] => Some (st, racc)
  | b :: r =>
    match cb_recycle_list st (qb_chunks b) racc with
    | None => None
    | Some (st1, racc1) =>
      (* [comment removed for export] *)
      if negb (in_primary st1 (qb_addr b)) then None else
      match cache_dealloc st1 (class_of_addr st1 (qb_addr b)) (qb_addr b) with
      | None => None
      | Some (st2, ev2) => do_recycle st2 r (rev_append ev2 racc1)
      end
    end
  end.

(* [comment removed for export] *)
Fixpoint merge_batches_aux (fuel : nat) (cur : qbatch) (rest : list qbatch) (racc_done : list qbatch)
         (rextracted : list qbatch) (xbytes : Z) : option (list qbatch * list qbatch * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
    match rest with
    | [] => Some (rev (cur :: racc_done), rev rextracted, xbytes)
    | nx :: rest' =>
      if qb_count cur + qb_count nx <=? kBatchCount then
        if qb_size cur <? kBatchSize then None else                       (* [comment removed for export] *)
        let cur' := mkQB (qb_addr cur) (qb_size cur + (qb_size nx - kBatchSize)) (qb_count cur + qb_count nx)
                         (qb_chunks cur ++ qb_chunks nx) in
        let nx'  := mkQB (qb_addr nx) kBatchSize 0 [] in
        merge_batches_aux fuel' cur' rest' racc_done (nx' :: rextracted) (xbytes + kBatchSize)
      else merge_batches_aux fuel' nx rest' (cur :: racc_done) rextracted xbytes
    end
  end.
Definition merge_batches : ltac2:(zQ "60!khb!im1!jq7!kjc!h9!in6>1q$1@1$3@2$0@2$0$1@1$2$5$4") := ltac2:(zQ "h10!in6!jq7!khb!h9!im1!kjc!ki2!ig4!lgc!kk5!qh1!oj7!qh5!ima!qia!qj5!o5\1q$4M1\1x@1$1$0@1$5@2$2@2$2$4@1$1$0$3@1$f^1@2$8@2$2@2$2$4@1$1$0$3@4$6@2$2$4@1$1$0$3@4$6$4@1$1$0^1@1$7$0Z\1b$0\1r@1$1$0M5\1x@1$5@2$2@2$2@1$1$0@1$1$0$3@1$5@2$2@2$2$4@1$1$0$3@6$c@1$a@2$b$0^1^2^1@1$7$0@1$7$0Z\1p@2$2@2$2@1$1$0@1$1$0$3M2\1p@2$2@2$2@1$1$0@1$1$0$3@1$5@2$2@2$2$4@1$1$0$3^1\2p0@2$2@1$1$0@1$1$0\2xb$3M2\2p0@2$2@1$1$0@1$1$0@1$5@2$2@2$2$4@1$1$0$3^2\2l'@1$1$0\2ex@1$1$0@2$8@2$2@2$2$4@1$1$0$3@4$6@2$2$4@1$1$0$3@4$6$4@1$1$0@2$d^2@2$h0@1$e^8^3^1^3@1$9@2$2@2$2$4@1$1$0$3").

(* [comment removed for export] *)
Fixpoint pop_while (fuel : nat) (l : list qbatch) (bytes : Z) (min_size : Z) (acc : list qbatch)
  : option (list qbatch * Z * list qbatch) :=
  match fuel with
  | O => None
  | S f =>
    if bytes <=? min_size then Some (l, bytes, acc)
    else match l with
         | [] => None                                                       (* [comment removed for export] *)
         | b :: r => pop_while f r (bytes - qb_size b) min_size (b :: acc)  (* [comment removed for export] *)
         end
  end.

(* [comment removed for export] *)
Definition quarantine_recycle : ltac2:(zQ "60!inf!jq7!kjc!khb!h9!lg3>2st$0>8min_size$4@1$2@2$3$0@1$1$5") := ltac2:(zQ "he0!khb!jq7!in6!kjc!im1!inf!lg3!h9!kk5!rb!qia!lgc!ig4!ki2!qj5!hj6!pd!qjf!qh1!s8!lv1!oj7!itf!qk6!ql3!qm0!ima!qn0!qnc!qo5\2st$5\8min_size$7=1g$4@1$h6^2=8overhead$7@2$h0@2$hd$2@1$e^1$h8M9\0$9@1$3@2$0$5@1$1$6@2$f@1$a^2^1@1$8@2$0$5@1$1$6=6merged@1$3@2$0$4@1$1$2M9\0$9@1$3@2$0$4@1$1$2@2$h3@2$f^1@1$a^2@2$f@2$h0@1$a^2+m4@2$h0^1+s8M3\1x@1$3@2$0@2$0$4@1$1$2$7@1$3@2$0$4@1$1$2@1$h9^2\1p@2$0@2$0$4@1$1$2$7M0\1p@2$0@2$0$4@1$1$2$7@1$3@2$0$4@1$1$2^1\2p0@2$0$4@1$1$2\1z$7M0\2p0@2$0$4@1$1$2@1$3@2$0$4@1$1$2^2\2g'$4\2ex@1$1$2@2$b@2$0$4@1$1$2@4$d$4@1$1$2^2^1@1$8@2$0$4@1$1$2@2$b@2$0$4@1$1$2@4$d$4@1$1$2^2@1$c$2M3\6merged@1$3@2$0$4@1$1$2@1$3@2$0$5@1$1$6^1\1p@2$0$4@1$1$2M0\1p@2$0$4@1$1$2@1$3@2$0$5@1$1$6^1\2g1$4\9extracted@1$1$2M3\1x@1$3@2$0@2$0@1$1$2$7@1$1$2@1$3@2$0$5@1$1$6@5$hb@1$h2@2$h5$2@1$e^2@1$e^2@1$a^2^7@1$c$2\1p@2$0@2$0@1$1$2$7@1$1$2M0\1p@2$0@2$0@1$1$2$7@1$1$2@1$3@2$0$5@1$1$6^1\2p0@2$0@1$1$2$7\7rpopped@1$1$2M0\2p0@2$0@1$1$2$7@1$3@2$0$5@1$1$6^2\2l2@1$1$2\6bytes2$7=3st1$5@2$hc^d@2$ha^2^1M3\1x@1$3@2$0$5@1$1$6@1$3@2$0$5@1$1$6@3$h7^1@3$h4$2^7@2$h1$2^4@1$c$6\1p@2$0$5@1$1$6M0\1p@2$0$5@1$1$6@1$3@2$0$5@1$1$6^1\3st2$5\4racc@1$1$6@2$b@2$0$5@1$1$6@4$d$5@1$1$6^2@2$h1$6^1@1$8@2$0$5@1$1$6@1$8@2$0$5@1$1$6@1$8@2$0$5@1$1$6").

(* [comment removed for export] *)
Definition quarantine_drain : ltac2:(zQ "50!inf!jq7!kjc!khb!lg3>2st$0@1$2@2$3$0@1$1$4") := ltac2:(zQ "h90!inf!lg3!jq7!qia!im1!rb!khb!qj5!lgc!lv1!ig4!kjc!ki2!itf!jj0!jja!jm8!ima!in6!qoc!qp6!qnc!qqc!p1!hj6\2st$0=1t$4@1$h0^1=1g$4@1$d^2=2g1$4@2$h1@3$9$h2@1$7^1@1$7^2@2$h7@1$3^1@1$3^2=3st1$0@2$h5@2$h6^4$h3^1M5\0$5@1$b@2$6$0@1$2$1@2$h8@1$e^5@1$3^2@2$h4^1@1$f^5@2$8@2$6$0@1$2$1@4$c$0@1$2$1^1@1$a$1").

(* [comment removed for export] *)
Definition quarantine_enqueue : ltac2:(zQ "60!h9!inf!jq7!kjc!khb!lg3>2st$1>1m$0>4size$0@1$3@2$4$1@1$2$5") := ltac2:(zQ "i60!jq7!khb!inf!in6!lg3!h9!ig4!kjc!rb!p1!jud!qr5!qj5!lv1!jm8!im1!kk5!lgc!ki2!ql3!ima!qrc!qia!qqc!qs7!oj7!hg5!jq0!oi9!nha!ota!qsf!qtd!qub!qv5!rg1!hh4!s2\2st$2\1m$5\4size$5=1t$f@1$e^3=8need_new$8M0\1x@1$0$3$8@1$c^1$hb\1q$3\1l@1$0$3@2$i5$i0@1$h5@3$h8$3@1$c^3@4$bZZZ@1$6$5M8\8need_new$8@1$7@2$1$2@1$0$4^1M7\1x@1$7@2$1@2$1$2$5@1$0$4@1$7@2$1$2@1$0$4@2$he^5$hf\1p@2$1@2$1$2$5@1$0$4M1\1p@2$1@2$1$2$5@1$0$4@1$7@2$1$2@1$0$4^1\2p0@2$1$2$5\2ev@1$0$4M1\2p0@2$1$2$5@1$7@2$1$2@1$0$4^2\3st1$2\1b$5M8\0$8@1$7@2$1$2@1$0$4@2$i4^1Z@1$h0@2$1$2@1$0$4=2nb$3@4$b^1@2$9^8$h3+1@3$a$5^9@1$6$5=2t1$f@2$h4@3$d$3@1$c@1$e^3@3$a$3^1@1$6$3@2$9@2$9@1$h6@1$e^3^9$h3@2$h1@2$1$2@1$0$4@4$h2$2@1$0$4@2$h7^4^1^5@1$h0@2$1$2@1$0$4=1l@1$0$3@1$c^2=1k$ha@2$h9$3^1=2lb$3@3$h8$3^2@4$bZZZ@1$6$5=3lb'$3@4$b@1$i1^1@2$9@1$i3^1^6@2$9@1$h5^1+1@3$d$5@1$i2^1@3$a$5^7@1$6$5=2t1$f@2$h4@3$d$3@3$hd$3@2$hc^3N1^4@3$a$3^1@1$6$3@2$9@1$h6^6^7@2$h1@2$1$2@1$0$4@4$h2$2@1$0$4@2$h7^a^1@1$6$4").

(* [comment removed for export] *)
Definition quarantine_put : ltac2:(zQ "60!inf!jq7!kjc!khb!ii5!lg3>2st$0>2ch$4@1$2@2$3$0@1$1$5") := ltac2:(zQ "hb2!lg3!inf!jq7!khb!kjc!kk5!rb!lv1!lgc!ki2!ji4!hj6!sf!h9!jj0!jm8!rgb!psd!ijf!ii5!rha!mn6!qia!rj0!rk4!hr4!hh4&\1x@1$4@2$3$1@1$2$0@1$4@2$3$1@1$2$0&\1p@2$3$1@1$2$0@1$4@2$3$1@1$2$0\2st$1\2ch$h3=4size$d@1$h1^1M6\0$6@1$4@2$3$1@1$2$0@2$c@2$ha@1$a^3Z@2$b@1$e^3^1@1$5@2$3$1@1$2$0M4~0@4$h5^3@1$h2^2@2$h9^1+8$h4\1p@2$3$1@1$2$0M3~1^1\3st1$1\3ev1@1$2$0M4~0@3$h8^2@1$h0^5^4\1p@2$3$1@1$2$0M3~1^1\3st2$1\3ev2@1$2$0M6\0$6@1$4@2$3$1@1$2$0@2$b@1$a^2@1$h6@1$f^2M4~0@1$h7^2\1p@2$3$1@1$2$0M3~1^1\3st3$1\3ev3@1$2$0@2$8@2$3$1@1$2$0@4$9$1@1$2$0^2@3$7$0^7@3$7$0^4^1@1$5@2$3$1@1$2$0@2$8@2$3$1@1$2$0@4$9$1@1$2$0^2@3$7$0^4^1@1$5@2$3$1@1$2$0@1$5@2$3$1@1$2$0").

(* [comment removed for export] *)
Definition am_free_full (st : astate) (p : Z) : option (astate * list effect) :=
  let '(st0, ev0) := if as_internal_init st then (st, []) else (set_internal_init st, [EInternalAllocInit]) in
  if p =? 0 then Some (st0, ev0) else
  match find_chunk (as_chunks st0) p with
  | None => None                                                               (* [comment removed for export] *)
  | Some ch =>
    match ch_state ch with
    | CQuarantine => None                                                       (* [comment removed for export] *)
    | CAllocated =>
      let ch' := mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine in
      let st1 := upd_chunk st0 ch' in
      let ev1 := [EStore64 p 0xFFFFFFFF00000000; EStore64 p 0 (* [comment removed for export] *)] in
      match quarantine_put st1 ch' with
      | None => None
      | Some (st2, ev2) => Some (st2, ev0 ++ ev1 ++ ev2)
      end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive syscall_event :=
  | SysMmap (hint len prot flags ret : Z)
  | SysMunmap (addr len : Z).

Fixpoint syscalls_of (l : list effect) : list syscall_event :=
  match l with
  | [] => []
  | EMmap h n pr fl r :: t => SysMmap h n pr fl r :: syscalls_of t
  | EMunmap a n :: t => SysMunmap a n :: syscalls_of t
  | _ :: t => syscalls_of t
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition init_state_q : ltac2:(zQ "40!h9!rb!jq7!inf>8res_base$0>9space_beg$0>9ptr_array$0>3env@1$2$0>ctrack_shadow$1>4qmax$0>4qmin$0>6qcache$0$3") := ltac2:(zQ "hd0!h9!ju3!jud!lr5!ig4!lt1!khb!jq0!rla!qoc!rm6!rb!jq7!rn0!ro8!rq1!lld!ii5!li4!rr0!kv6!jo2!ih5!jp6!hvb!ip5!jqe!rs4!p1\8res_base$0\9space_beg$0\9ptr_array$0\3env@1$c$0\ctrack_shadow$b\4qmax$0\4qmin$0\6qcache$0@h2$h5^7^6@3$a$h8$h9Ni0$3@3$a$h6$h7Ni0Z@1$4$ha@1$hb$h1$9$9$3@3$2$1@5$5^8+igggghhgg0$d$8$7@3$2$1@5$5@2$hc^7$h4$h2$f$h0$3@3$2$1@5$5^6$h3$e$8$7@1$4$1@1$4@2$6@2$6$0$0$0^5^4^3^2^1").
Definition init_state : ltac2:(zQ "40!h9!rb!jq7!inf>8res_base$0>9space_beg$0>9ptr_array$0>3env@1$2$0>ctrack_shadow$1$3") := ltac2:(zQ "70!h9!rb!jq7!rsd!rtc!ruc!sg2\8res_base$0\9space_beg$0\9ptr_array$0\3env@1$2$0\ctrack_shadow$1@8$3^5^4^3^2^1$5$6$4").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition ex_state : ltac2:(zQ "10!inf$0") := ltac2:(zQ "50!h9!jud!ig4!jq0!sh8@5$4+iqqqqqukpgg0+iqqqqqulggg0+iqsqqqulqgg0@3$1$0+iqsqqsqnqgg0@1$2$0$3").
Definition ex1 : ltac2:(zQ "60!khb!jq7!kjc!h9!inf!lg3@1$2@2$0@2$0$3$4@1$1$5") := ltac2:(zQ "20!si5!sj6@2$0$1+hggg0").

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WF.

  (* [comment removed for export] *)

  Variable st : astate.

  (* [comment removed for export] *)

  (* [comment removed for export] *)


  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

End WF.

(* [comment removed for export] *)
