(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr Frame.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_FUZZ                       : Z := 0xa3808.   (* [comment removed for export] *)
Definition P_A_STREAM_CTOR                : Z := 0xa4284.   (* [comment removed for export] *)
Definition P_A_STREAM_CLOSE_REMOTE        : Z := 0xa46f0.   (* [comment removed for export] *)
Definition P_A_PARSER_DTOR                : Z := 0xa4b0c.   (* [comment removed for export] *)
Definition P_A_STREAM_DTOR                : Z := 0xa4cc8.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_MAKE_SVC_CONFIG            : Z := 0xa5c60.   (* [comment removed for export] *)
Definition P_A_DESTROY_ALLOC_CONFIG       : Z := 0xa5e70.   (* [comment removed for export] *)
Definition P_A_CONFIG_SHUTDOWN            : Z := 0xa5edc.   (* [comment removed for export] *)
Definition P_A_CONFIG_GET_VALUE           : Z := 0xa5ee4.   (* [comment removed for export] *)
Definition P_A_DEALLOC_OBJ_CONFIG         : Z := 0xa6148.   (* [comment removed for export] *)
Definition P_A_DO_ADD_SERVICE             : Z := 0xa6238.   (* [comment removed for export] *)
Definition P_A_THROW_INVALID_SERVICE_OWNER : Z := 0xa6758.   (* [comment removed for export] *)
Definition P_A_THROW_SERVICE_ALREADY_EXISTS : Z := 0xa67b0.   (* [comment removed for export] *)
Definition P_A_DESTROY_ADDED              : Z := 0xa6808.   (* [comment removed for export] *)
Definition P_A_STD_THROW_BAD_ARRAY_NEW_LENGTH : Z := 0xa8010.   (* [comment removed for export] *)
Definition P_A_ALLOCIMPL_DESTROY          : Z := 0xa8048.   (* [comment removed for export] *)
Definition P_A_ALLOCIMPL_ALLOCATE         : Z := 0xa80bc.   (* [comment removed for export] *)
Definition P_A_ALLOCIMPL_DEALLOCATE       : Z := 0xa8478.   (* [comment removed for export] *)
Definition P_A_ALLOCIMPL_BASE_DTOR        : Z := 0xa8558.   (* [comment removed for export] *)
Definition P_A_THROW_BAD_ALLOC            : Z := 0xa8564.   (* [comment removed for export] *)
Definition P_A_ALLOC_OBJ_REGISTRY         : Z := 0xa8d38.   (* [comment removed for export] *)
Definition P_A_THROW_SYSTEM_ERROR         : Z := 0xa98b0.   (* [comment removed for export] *)
Definition P_A_MAKE_SVC_SCHED             : Z := 0xab34c.   (* [comment removed for export] *)
Definition P_A_ALLOC_OBJ_SCHED            : Z := 0xab460.   (* [comment removed for export] *)
Definition P_A_DESTROY_ALLOC_SCHED        : Z := 0xab5cc.   (* [comment removed for export] *)
Definition P_A_SCHED_GET_DEFAULT_TASK     : Z := 0xab630.   (* [comment removed for export] *)
Definition P_A_SCHED_CTOR                 : Z := 0xab6b0.   (* [comment removed for export] *)
Definition P_A_DO_USE_SERVICE             : Z := 0xac228.   (* [comment removed for export] *)
Definition P_A_CREATE_CONFIG              : Z := 0xafa68.   (* [comment removed for export] *)
Definition P_A_CONFIG_GET_BOOL            : Z := 0xafcec.   (* [comment removed for export] *)
Definition P_A_THROW_OUT_OF_RANGE         : Z := 0xb01a0.   (* [comment removed for export] *)
Definition P_A_CONFIG_GET_INT             : Z := 0xb0a14.   (* [comment removed for export] *)
Definition P_A_OPQUEUE_DTOR               : Z := 0xb2c70.   (* [comment removed for export] *)
Definition P_A_CEM_SCOPED_LOCK            : Z := 0xb2f68.   (* [comment removed for export] *)
Definition P_A_CEM_CTOR                   : Z := 0xb3704.   (* [comment removed for export] *)
Definition P_A_SCHED_DTOR                 : Z := 0xb3c74.   (* [comment removed for export] *)
Definition P_A_SCHED_DELDTOR              : Z := 0xb3f88.   (* [comment removed for export] *)
Definition P_A_SCHED_SHUTDOWN             : Z := 0xb3fb4.   (* [comment removed for export] *)
Definition P_A_POSIX_EVENT_CTOR           : Z := 0xb45e8.   (* [comment removed for export] *)
Definition P_A_CONFIG_GET_LONG            : Z := 0xb4af0.   (* [comment removed for export] *)
Definition P_A_POSIX_EVENT_SIGNAL_ALL     : Z := 0xb69c4.   (* [comment removed for export] *)
Definition P_A_DEALLOC_OBJ_SCHED          : Z := 0xb7cfc.   (* [comment removed for export] *)
Definition P_A_DEALLOC_OBJ_REGISTRY       : Z := 0xb7dec.   (* [comment removed for export] *)
Definition P_A_PARSER_DTOR_THUNK          : Z := 0xb7ea8.   (* [comment removed for export] *)
Definition P_A_ON_REQUEST_IMPL            : Z := 0xb7ed4.   (* [comment removed for export] *)
Definition P_A_ON_RESPONSE_IMPL           : Z := 0xb7ef0.   (* [comment removed for export] *)
Definition P_A_ON_FIELD_IMPL              : Z := 0xb7ef4.   (* [comment removed for export] *)
Definition P_A_ON_TRAILER_FIELD_IMPL      : Z := 0xb7efc.   (* [comment removed for export] *)
Definition P_A_ON_HEADER_IMPL             : Z := 0xb8058.   (* [comment removed for export] *)
Definition P_A_ON_BODY_INIT_IMPL          : Z := 0xb807c.   (* [comment removed for export] *)
Definition P_A_ON_BODY_IMPL               : Z := 0xb80ec.   (* [comment removed for export] *)
Definition P_A_ON_CHUNK_HEADER_IMPL       : Z := 0xb8118.   (* [comment removed for export] *)
Definition P_A_ON_CHUNK_BODY_IMPL         : Z := 0xb816c.   (* [comment removed for export] *)
Definition P_A_ON_FINISH_IMPL             : Z := 0xb81d8.   (* [comment removed for export] *)
Definition P_A_FIELDS_DTOR                : Z := 0xb81fc.   (* [comment removed for export] *)
Definition P_A_MB_DTOR                    : Z := 0xb8258.   (* [comment removed for export] *)
Definition P_A_FIELDS_DELETE_LIST         : Z := 0xb8300.   (* [comment removed for export] *)
Definition P_A_FIELDS_REALLOC_STRING      : Z := 0xb83ec.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_ON_REQUEST_IMPL_T          : Z := 0xb8b04.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_HEADER_SET_METHOD          : Z := 0xb8dcc.   (* [comment removed for export] *)
Definition P_A_HEADER_SET_VERSION         : Z := 0xb9070.   (* [comment removed for export] *)
Definition P_A_FIELDS_REALLOC_TARGET      : Z := 0xb93b4.   (* [comment removed for export] *)
Definition P_A_STRING_TO_VERB             : Z := 0xb9e68.   (* [comment removed for export] *)
Definition P_A_SV_INDEX                   : Z := 0xba638.   (* [comment removed for export] *)
Definition P_A_SV_REMOVE_PREFIX           : Z := 0xba6d4.   (* [comment removed for export] *)
Definition P_A_FIELDS_INSERT              : Z := 0xba78c.   (* [comment removed for export] *)
Definition P_A_FIELDS_NEW_ELEMENT         : Z := 0xba8c8.   (* [comment removed for export] *)
Definition P_A_FIELDS_INSERT_ELEMENT      : Z := 0xbab28.   (* [comment removed for export] *)
Definition P_A_FIELDS_VALUE_TYPE_CTOR     : Z := 0xbaff8.   (* [comment removed for export] *)
Definition P_A_LIST_ITERATOR_TO           : Z := 0xbb1cc.   (* [comment removed for export] *)
Definition P_A_RB_UPPER_BOUND_LOOP        : Z := 0xbb260.   (* [comment removed for export] *)
Definition P_A_KEY_COMPARE_SV_VT          : Z := 0xbb360.   (* [comment removed for export] *)
Definition P_A_FIELDS_FIND_SV             : Z := 0xbb474.   (* [comment removed for export] *)
Definition P_A_LIST_ITERATOR_TO_C         : Z := 0xbb510.   (* [comment removed for export] *)
Definition P_A_RB_FIND                    : Z := 0xbb5a4.   (* [comment removed for export] *)
Definition P_A_RB_LOWER_BOUND_LOOP        : Z := 0xbb6a0.   (* [comment removed for export] *)
Definition P_A_KEY_COMPARE_VT_SV          : Z := 0xbb790.   (* [comment removed for export] *)
Definition P_A_RB_INSERT_BEFORE           : Z := 0xbb8a4.   (* [comment removed for export] *)
Definition P_A_RB_REBALANCE               : Z := 0xbb99c.   (* [comment removed for export] *)
Definition P_A_RB_INSERT_COMMIT           : Z := 0xbbf90.   (* [comment removed for export] *)
Definition P_A_RB_PREV_NODE               : Z := 0xbc154.   (* [comment removed for export] *)
Definition P_A_RB_IS_HEADER               : Z := 0xbc23c.   (* [comment removed for export] *)
Definition P_A_FIELDS_INDEX_F             : Z := 0xbc310.   (* [comment removed for export] *)
Definition P_A_TOKEN_LIST_EXISTS          : Z := 0xbc3ec.   (* [comment removed for export] *)
Definition P_A_FIELDS_FIND_F              : Z := 0xbc868.   (* [comment removed for export] *)
Definition P_A_FIELD_TABLE_CTOR           : Z := 0xbc9b4.   (* [comment removed for export] *)
Definition P_A_FIELD_TABLE_DIGEST         : Z := 0xbcb58.   (* [comment removed for export] *)
Definition P_A_TOKEN_LIST_ITER_INCR       : Z := 0xbccd8.   (* [comment removed for export] *)
Definition P_A_TOKEN_LIST_ITER_CTOR       : Z := 0xbcfec.   (* [comment removed for export] *)
Definition P_A_READER_PUT                 : Z := 0xbd2bc.   (* [comment removed for export] *)
Definition P_A_MB_DYN_PREPARE             : Z := 0xbd6fc.   (* [comment removed for export] *)
Definition P_A_MB_COMMIT                  : Z := 0xbdb9c.   (* [comment removed for export] *)
Definition P_A_MB_PREPARE                 : Z := 0xbde50.   (* [comment removed for export] *)
Definition P_A_MB_LIST_ITERATOR_TO        : Z := 0xbe9dc.   (* [comment removed for export] *)
Definition P_A_MB_ALLOC                   : Z := 0xbea70.   (* [comment removed for export] *)
Definition P_A_MB_SUBRANGE_CTOR           : Z := 0xbed04.   (* [comment removed for export] *)
Definition P_A_MB_SUBRANGE_DEREF          : Z := 0xbfb48.   (* [comment removed for export] *)
Definition P_A_BUFFER_COPY_MB             : Z := 0xbfcb0.   (* [comment removed for export] *)
Definition P_A_STDFUNC_CALL_CB_H          : Z := 0xbfe50.   (* [comment removed for export] *)
Definition P_A_STDFUNC_CALL_CB_B          : Z := 0xc0114.   (* [comment removed for export] *)
Definition P_A_STD_THROW_LENGTH_ERROR     : Z := 0xc0554.   (* [comment removed for export] *)
Definition P_A_SSVC_MAKE_IMPL             : Z := 0xc05ac.   (* [comment removed for export] *)
Definition P_A_SP_STATE_ARROW             : Z := 0xc06f0.   (* [comment removed for export] *)
Definition P_A_FB_PREPARE                 : Z := 0xc0768.   (* [comment removed for export] *)
Definition P_A_MAKE_SHARED_STATE          : Z := 0xc0d08.   (* [comment removed for export] *)
Definition P_A_SP_IMPL_ARROW              : Z := 0xc12a4.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_ANYEX_QUERY_CONTEXT        : Z := 0xc131c.   (* [comment removed for export] *)
Definition P_A_THROW_BAD_EXECUTOR         : Z := 0xc16b4.   (* [comment removed for export] *)
Definition P_A_CREATE_SSVC                : Z := 0xc1eb8.   (* [comment removed for export] *)
Definition P_A_ALLOC_OBJ_SSVC             : Z := 0xc1f2c.   (* [comment removed for export] *)
Definition P_A_DESTROY_ALLOC_SSVC         : Z := 0xc20b8.   (* [comment removed for export] *)
Definition P_A_MAKE_SHARED_IMPL           : Z := 0xc211c.   (* [comment removed for export] *)
Definition P_A_SSVC_DTOR                  : Z := 0xc2348.   (* [comment removed for export] *)
Definition P_A_SSVC_DELDTOR               : Z := 0xc2390.   (* [comment removed for export] *)
Definition P_A_SSVC_SHUTDOWN              : Z := 0xc23f0.   (* [comment removed for export] *)
Definition P_A_NONCOPYABLE_DTOR           : Z := 0xc2834.   (* [comment removed for export] *)
Definition P_A_SHCOUNT_CTOR_IMPL          : Z := 0xc2838.   (* [comment removed for export] *)
Definition P_A_SHCOUNT_DTOR               : Z := 0xc29a8.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_DTOR             : Z := 0xc2af0.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_DELDTOR          : Z := 0xc2b38.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_DISPOSE          : Z := 0xc2b98.   (* [comment removed for export] *)
Definition P_A_SPCB_DESTROY               : Z := 0xc2ba0.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_GET_DEL          : Z := 0xc2bf8.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_GET_LDEL         : Z := 0xc2c54.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_GET_UDEL         : Z := 0xc2c5c.   (* [comment removed for export] *)
Definition P_A_SPMSD_IMPL_DESTROY         : Z := 0xc2c64.   (* [comment removed for export] *)
Definition P_A_VEC_READOP_RESERVE         : Z := 0xc2f6c.   (* [comment removed for export] *)
Definition P_A_VEC_READOP_THROW_LEN       : Z := 0xc3284.   (* [comment removed for export] *)
Definition P_A_SPLITBUF_READOP_DTOR       : Z := 0xc3408.   (* [comment removed for export] *)
Definition P_A_ALLOC_AT_LEAST_READOP      : Z := 0xc3588.   (* [comment removed for export] *)
Definition P_A_VEC_READOP_DESTROY         : Z := 0xc3840.   (* [comment removed for export] *)
Definition P_A_DEALLOC_OBJ_SSVC           : Z := 0xc3a70.   (* [comment removed for export] *)
Definition P_A_SHCOUNT_CTOR_STATE         : Z := 0xc3b60.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_DTOR            : Z := 0xc3cd0.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_DELDTOR         : Z := 0xc3d70.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_DISPOSE         : Z := 0xc3df8.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_GET_DEL         : Z := 0xc3e78.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_GET_LDEL        : Z := 0xc3ed4.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_GET_UDEL        : Z := 0xc3edc.   (* [comment removed for export] *)
Definition P_A_STATE_DTOR                 : Z := 0xc3ee4.   (* [comment removed for export] *)
Definition P_A_ANYEX_COPY                 : Z := 0xc4368.   (* [comment removed for export] *)
Definition P_A_ANYEX_MOVE                 : Z := 0xc447c.   (* [comment removed for export] *)
Definition P_A_SPLITBUF_STATEP_DTOR       : Z := 0xc68bc.   (* [comment removed for export] *)
Definition P_A_VEC_STATEP_THROW_LEN       : Z := 0xc6990.   (* [comment removed for export] *)
Definition P_A_ALLOC_AT_LEAST_STATEP      : Z := 0xc69a8.   (* [comment removed for export] *)
Definition P_A_ANYEX_FN_DESTROY           : Z := 0xc84cc.   (* [comment removed for export] *)
Definition P_A_ANYEX_FN_COPY              : Z := 0xc84d0.   (* [comment removed for export] *)
Definition P_A_ANYEX_FN_MOVE              : Z := 0xc8544.   (* [comment removed for export] *)
Definition P_A_ANYEX_FN_TARGET            : Z := 0xc85b8.   (* [comment removed for export] *)
Definition P_A_ANYEX_FN_QUERY_CTX         : Z := 0xc85bc.   (* [comment removed for export] *)
Definition P_A_STREAM_CLOSE               : Z := 0xcae38.   (* [comment removed for export] *)
Definition P_A_STATE_REMOVE               : Z := 0xcb758.   (* [comment removed for export] *)
Definition P_A_SYNC_READ_OP               : Z := 0xcba70.   (* [comment removed for export] *)
Definition P_A_HTTP_READ_SOME             : Z := 0xcbbfc.   (* [comment removed for export] *)
Definition P_A_FB_DYN_PREPARE             : Z := 0xcc500.   (* [comment removed for export] *)
Definition P_A_STREAM_READ_SOME           : Z := 0xcc6c8.   (* [comment removed for export] *)
Definition P_A_BP_PUT_EOF                 : Z := 0xcceb4.   (* [comment removed for export] *)
Definition P_A_BP_PUT                     : Z := 0xcd0d8.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_START_LINE        : Z := 0xcdce4.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_FIELDS            : Z := 0xce0a8.   (* [comment removed for export] *)
Definition P_A_BP_FINISH_HEADER           : Z := 0xce468.   (* [comment removed for export] *)
Definition P_A_BP_CONTENT_LENGTH          : Z := 0xce904.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_BODY              : Z := 0xcea44.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_BODY_TO_EOF       : Z := 0xcec74.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_CHUNK_HEADER      : Z := 0xcee1c.   (* [comment removed for export] *)
Definition P_A_BP_INNER_PARSE_START_LINE  : Z := 0xcf6fc.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_VERSION           : Z := 0xcfe90.   (* [comment removed for export] *)
Definition P_A_BP_INNER_PARSE_FIELDS      : Z := 0xd0474.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_FIELD             : Z := 0xd0afc.   (* [comment removed for export] *)
Definition P_A_BP_DO_FIELD                : Z := 0xd17cc.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_STRING_TO_FIELD            : Z := 0xd2a98.   (* [comment removed for export] *)
Definition P_A_FIELD_TABLE_EQUALS         : Z := 0xd2bc8.   (* [comment removed for export] *)
Definition P_A_VALIDATE_OPT_TOKEN_LIST    : Z := 0xd2e68.   (* [comment removed for export] *)
Definition P_A_BP_DO_FIELD_LAMBDA         : Z := 0xd2f14.   (* [comment removed for export] *)
Definition P_A_OPT_TOKEN_LIST_INCR        : Z := 0xd2fbc.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_CHUNK_EXT         : Z := 0xd32c8.   (* [comment removed for export] *)
Definition P_A_EC_ASSIGN_HTTP             : Z := 0xd39ac.   (* [comment removed for export] *)
Definition P_A_READ_SIZE_FB               : Z := 0xd3b10.   (* [comment removed for export] *)
Definition P_A_CXA_GUARD_ACQUIRE          : Z := 0xd3c84.   (* [comment removed for export] *)
Definition P_A_CXA_GUARD_RELEASE          : Z := 0xd3cd4.   (* [comment removed for export] *)
Definition P_A_STD_TERMINATE              : Z := 0xd3d04.   (* [comment removed for export] *)
Definition P_A_OPDEL                      : Z := 0xf0560.   (* [comment removed for export] *)
Definition P_A_OPDEL2                     : Z := 0xf0564.   (* [comment removed for export] *)
Definition P_A_OPDEL_ARR                  : Z := 0xf0568.   (* [comment removed for export] *)
Definition P_A_STD_ALIGN                  : Z := 0xf1e64.   (* [comment removed for export] *)
Definition P_A_STD_THROW_SYSTEM_ERROR     : Z := 0xf5e60.   (* [comment removed for export] *)
Definition P_A_CV_DTOR                    : Z := 0xf5fc4.   (* [comment removed for export] *)
Definition P_A_CV_NOTIFY_ALL              : Z := 0xf5ffc.   (* [comment removed for export] *)
Definition P_A_CV_WAIT                    : Z := 0xf6018.   (* [comment removed for export] *)
Definition P_A_MTX_DTOR                   : Z := 0xf6194.   (* [comment removed for export] *)
Definition P_A_MTX_LOCK                   : Z := 0xf61b0.   (* [comment removed for export] *)
Definition P_A_MTX_UNLOCK                 : Z := 0xf61f8.   (* [comment removed for export] *)
Definition P_A_ERRNO_LOCATION             : Z := 0xfefa0.   (* [comment removed for export] *)
Definition P_A_ASSERT_FAIL                : Z := 0xff098.   (* [comment removed for export] *)
Definition P_A_FREE                       : Z := 0x73274.   (* [comment removed for export] *)
Definition P_A_MALLOC                     : Z := 0x73278.   (* [comment removed for export] *)
Definition P_A_TOWRITE                    : Z := 0x1057a0.   (* [comment removed for export] *)
Definition P_A_FWRITEX                    : Z := 0x1057f4.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_VFPRINTF                   : Z := 0x105c88.   (* [comment removed for export] *)
Definition P_A_PRINTF_CORE                : Z := 0x105e38.   (* [comment removed for export] *)
Definition P_A_POP_ARG                    : Z := 0x106c68.   (* [comment removed for export] *)
Definition P_A_PAD                        : Z := 0x106d9c.   (* [comment removed for export] *)
Definition P_A_VSNPRINTF                  : Z := 0x10b430.   (* [comment removed for export] *)
Definition P_A_SN_WRITE                   : Z := 0x10b4fc.   (* [comment removed for export] *)
Definition P_A_SHLIM                      : Z := 0x1086c0.   (* [comment removed for export] *)
Definition P_A_SHGETC                     : Z := 0x1086f8.   (* [comment removed for export] *)
Definition P_A_STRTOLL                    : Z := 0x10cc14.   (* [comment removed for export] *)
Definition P_A_INTSCAN                    : Z := 0x10ae3c.   (* [comment removed for export] *)
Definition P_A_BCMP                       : Z := 0x10d678.   (* [comment removed for export] *)
Definition P_A_MEMCHR                     : Z := 0x10d67c.   (* [comment removed for export] *)
Definition P_A_MEMCMP                     : Z := 0x10d748.   (* [comment removed for export] *)
Definition P_A_MEMCPY                     : Z := 0x10d778.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_MEMSET                     : Z := 0x10db7c.   (* [comment removed for export] *)
Definition P_A_STRCMP                     : Z := 0x10dd90.   (* [comment removed for export] *)
Definition P_A_STRLEN                     : Z := 0x10de60.   (* [comment removed for export] *)
Definition P_A_PTHREAD_COND_BROADCAST     : Z := 0x10e72c.   (* [comment removed for export] *)
Definition P_A_PTHREAD_COND_DESTROY       : Z := 0x10e7a0.   (* [comment removed for export] *)
Definition P_A_PTHREAD_COND_INIT          : Z := 0x10e964.   (* [comment removed for export] *)
Definition P_A_PRIVATE_COND_SIGNAL        : Z := 0x10f108.   (* [comment removed for export] *)
Definition P_A_PTHREAD_CONDATTR_DESTROY   : Z := 0x10f598.   (* [comment removed for export] *)
Definition P_A_PTHREAD_CONDATTR_INIT      : Z := 0x10f5a0.   (* [comment removed for export] *)
Definition P_A_PTHREAD_CONDATTR_SETCLOCK  : Z := 0x10f5ac.   (* [comment removed for export] *)
Definition P_A_PTHREAD_MUTEX_DESTROY      : Z := 0x1106e0.   (* [comment removed for export] *)
Definition P_A_PTHREAD_MUTEX_INIT         : Z := 0x110708.   (* [comment removed for export] *)
Definition P_A_PTHREAD_MUTEX_LOCK         : Z := 0x110788.   (* [comment removed for export] *)
Definition P_A_PTHREAD_MUTEX_UNLOCK       : Z := 0x110c74.   (* [comment removed for export] *)
Definition P_A_VM_WAIT                    : Z := 0x1118d0.   (* [comment removed for export] *)
Definition P_A_OPNEW                      : Z := 0x114414.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ARVT_ALLOCIMPL       : Z := 0x115fb8.   (* [comment removed for export] *)
Definition AVP_ALLOCIMPL        : Z := 0x115fc8.
Definition AVS_ALLOCIMPL_0      : Z := 0xa8048.
Definition AVS_ALLOCIMPL_8      : Z := 0xa80bc.
Definition AVS_ALLOCIMPL_16     : Z := 0xa8478.
Definition AVS_ALLOCIMPL_24     : Z := 0xa8558.
Definition AVS_ALLOCIMPL_32     : Z := 0xa855c.
Definition ARVT_CONFIG_SVC      : Z := 0x115c58.   (* [comment removed for export] *)
Definition AVP_CONFIG_SVC       : Z := 0x115c68.
Definition AVS_CONFIG_SVC_0     : Z := 0xc2834.
Definition AVS_CONFIG_SVC_8     : Z := 0xa5ed4.
Definition AVS_CONFIG_SVC_16    : Z := 0xa5edc.
Definition AVS_CONFIG_SVC_24    : Z := 0xa5ee0.
Definition AVS_CONFIG_SVC_32    : Z := 0xa5ee4.
Definition ARVT_SCHED           : Z := 0x116390.   (* [comment removed for export] *)
Definition AVP_SCHED            : Z := 0x1163a0.
Definition AVS_SCHED_0          : Z := 0xb3c74.
Definition AVS_SCHED_8          : Z := 0xb3f88.
Definition AVS_SCHED_16         : Z := 0xb3fb4.
Definition AVS_SCHED_24         : Z := 0xa5ee0.
Definition ARVT_SSVC            : Z := 0x117310.   (* [comment removed for export] *)
Definition AVP_SSVC             : Z := 0x117320.
Definition AVS_SSVC_0           : Z := 0xc2348.
Definition AVS_SSVC_8           : Z := 0xc2390.
Definition AVS_SSVC_16          : Z := 0xc23f0.
Definition AVS_SSVC_24          : Z := 0xa5ee0.
Definition ARVT_SPCI_IMPL       : Z := 0x117370.   (* [comment removed for export] *)
Definition AVP_SPCI_IMPL        : Z := 0x117380.
Definition AVS_SPCI_IMPL_0      : Z := 0xc2af0.
Definition AVS_SPCI_IMPL_8      : Z := 0xc2b38.
Definition AVS_SPCI_IMPL_16     : Z := 0xc2b98.
Definition AVS_SPCI_IMPL_24     : Z := 0xc2ba0.
Definition AVS_SPCI_IMPL_32     : Z := 0xc2bf8.
Definition AVS_SPCI_IMPL_40     : Z := 0xc2c54.
Definition AVS_SPCI_IMPL_48     : Z := 0xc2c5c.
Definition ARVT_SPCI_STATE      : Z := 0x1173e0.   (* [comment removed for export] *)
Definition AVP_SPCI_STATE       : Z := 0x1173f0.
Definition AVS_SPCI_STATE_0     : Z := 0xc3cd0.
Definition AVS_SPCI_STATE_8     : Z := 0xc3d70.
Definition AVS_SPCI_STATE_16    : Z := 0xc3df8.
Definition AVS_SPCI_STATE_24    : Z := 0xc2ba0.
Definition AVS_SPCI_STATE_32    : Z := 0xc3e78.
Definition AVS_SPCI_STATE_40    : Z := 0xc3ed4.
Definition AVS_SPCI_STATE_48    : Z := 0xc3edc.
Definition ARVT_PARSER          : Z := 0x116478.   (* [comment removed for export] *)
Definition AVP_PARSER           : Z := 0x116488.
Definition AVS_PARSER_0         : Z := 0xa4b0c.
Definition AVS_PARSER_8         : Z := 0xb7ea8.
Definition AVS_PARSER_16        : Z := 0xb7ed4.
Definition AVS_PARSER_24        : Z := 0xb7ef0.
Definition AVS_PARSER_32        : Z := 0xb7ef4.
Definition AVS_PARSER_40        : Z := 0xb7efc.
Definition AVS_PARSER_48        : Z := 0xb8058.
Definition AVS_PARSER_56        : Z := 0xb807c.
Definition AVS_PARSER_64        : Z := 0xb80ec.
Definition AVS_PARSER_72        : Z := 0xb8118.
Definition AVS_PARSER_80        : Z := 0xb816c.
Definition AVS_PARSER_88        : Z := 0xb81d8.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARVT_SYSTEM_ECAT     : Z := 0x115a00.   (* [comment removed for export] *)
Definition AVP_SYSTEM_ECAT      : Z := 0x115a10.
Definition AVS_SYSTEM_ECAT_0    : Z := 0xa55f4.
Definition AVS_SYSTEM_ECAT_8    : Z := 0xa31b4.
Definition AVS_SYSTEM_ECAT_16   : Z := 0xa5074.
Definition AVS_SYSTEM_ECAT_24   : Z := 0xa51f0.
Definition AVS_SYSTEM_ECAT_32   : Z := 0xa5600.
Definition AVS_SYSTEM_ECAT_40   : Z := 0xa5644.
Definition AVS_SYSTEM_ECAT_48   : Z := 0xa5508.
Definition ARVT_GENERIC_ECAT    : Z := 0x1159a0.   (* [comment removed for export] *)
Definition AVP_GENERIC_ECAT     : Z := 0x1159b0.
Definition AVS_GENERIC_ECAT_0   : Z := 0xa5510.
Definition AVS_GENERIC_ECAT_8   : Z := 0xa3590.
Definition AVS_GENERIC_ECAT_16  : Z := 0xa5074.
Definition AVS_GENERIC_ECAT_24  : Z := 0xa51f0.
Definition AVS_GENERIC_ECAT_32  : Z := 0xa3170.
Definition AVS_GENERIC_ECAT_40  : Z := 0xa551c.
Definition AVS_GENERIC_ECAT_48  : Z := 0xa5508.
Definition ARVT_MISC_ECAT       : Z := 0x115b80.   (* [comment removed for export] *)
Definition AVP_MISC_ECAT        : Z := 0x115b90.

(* [comment removed for export] *)
Definition AT_ANYEX_TARGET_FNS      : Z := 0x1174e8.   (* [comment removed for export] *)
Definition AT_ANYEX_OBJECT_FNS      : Z := 0x1175a0.   (* [comment removed for export] *)
Definition AT_ANYEX_PROP_FNS        : Z := 0x1175c0.   (* [comment removed for export] *)
Definition AT_ANYEX_PROP_FNS_VOID   : Z := 0x117440.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AT_ANYEX_TARGET_FNS_words : list Z := [0xc6a70; 0xc6a7c; 0xc6c24; 0x0].
Definition AT_ANYEX_OBJECT_FNS_words : list Z := [0xc84cc; 0xc84d0; 0xc8544; 0xc85b8].
Definition AT_ANYEX_PROP_FNS_words : list Z := [0xc85bc; 0xc8614; 0xc867c; 0xc86e4; 0xc8790; 0xc887c; 0xc8968; 0xc8a14; 0xc8a7c; 0xc8b68; 0xc8be4; 0xc8c4c; 0xc8c68; 0xc8ce4; 0xc8d4c; 0xc8e34; 0xc8ee0; 0xc8f48; 0xc9034; 0xc90e0; 0xc9148].
Definition AT_ANYEX_PROP_FNS_VOID_words : list Z := [0xc45b8; 0xc4730; 0xc48a8; 0xc4a20; 0xc4b98; 0xc4d10; 0xc4e88; 0xc5000; 0xc5178; 0xc52f0; 0xc5468; 0xc55e0; 0xc5758; 0xc58d0; 0xc5a48; 0xc5bc0; 0xc5d38; 0xc5eb0; 0xc6028; 0xc61a0; 0xc6318].

(* [comment removed for export] *)
Definition AG_EXF_IN_CALLBACK       : Z := 0x65bad4.   (* [comment removed for export] *)
Definition AG_EXF_EMPTY             : Z := 0x65bae0.   (* [comment removed for export] *)
Definition AG_ASIO_SYSTEM_CAT       : Z := 0x65bb00.   (* [comment removed for export] *)
Definition AG_ASIO_NETDB_CAT        : Z := 0x65bb10.   (* [comment removed for export] *)
Definition AG_ASIO_ADDRINFO_CAT     : Z := 0x65bb20.   (* [comment removed for export] *)
Definition AG_ASIO_MISC_CAT         : Z := 0x65bb30.   (* [comment removed for export] *)
Definition AG_CALLSTACK_TOP_GUARD   : Z := 0x65bb48.   (* [comment removed for export] *)
Definition AG_ID_CONFIG             : Z := 0x65bb50.   (* [comment removed for export] *)
Definition AG_ID_SCHED              : Z := 0x65bb60.   (* [comment removed for export] *)
Definition AG_ID_REACTOR            : Z := 0x65bb70.   (* [comment removed for export] *)
Definition AG_ID_SSVC               : Z := 0x65bb80.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AG_FIELD_TABLE           : Z := 0x65bbd0.   (* [comment removed for export] *)
Definition AG_FIELD_TABLE_GUARD     : Z := 0x65c948.   (* [comment removed for export] *)
Definition AG_SYSTEM_CAT_INST       : Z := 0x11fa70.   (* [comment removed for export] *)
Definition AG_GENERIC_CAT_INST      : Z := 0x11fb88.   (* [comment removed for export] *)
Definition AG_INTEROP_CAT_INST      : Z := 0x11fb50.   (* [comment removed for export] *)
Definition AG_MISC_CAT_INST         : Z := 0x11fb18.   (* [comment removed for export] *)
Definition AG_STACK_CHK_GUARD       : Z := 0x67d4f0.   (* [comment removed for export] *)
Definition AG_GOT_STACK_CHK         : Z := 0x11c130.   (* [comment removed for export] *)
Definition AG_ERRNO                 : Z := 0x65d40c.   (* [comment removed for export] *)
Definition AG_TP                    : Z := 0x65d4b0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AW_SYSTEM_CAT_VPTR     : Z := 0x115a10.   (* [comment removed for export] *)
Definition W_SYSTEM_CAT_ID : Z := 0xb2ab117a257edfd1.
Definition AW_NETDB_CAT_VPTR      : Z := 0x115ad0.   (* [comment removed for export] *)
Definition W_NETDB_CAT_ID : Z := 0x0.
Definition AW_ADDRINFO_CAT_VPTR   : Z := 0x115b30.   (* [comment removed for export] *)
Definition W_ADDRINFO_CAT_ID : Z := 0x0.
Definition AW_MISC_CAT_VPTR       : Z := 0x115b90.   (* [comment removed for export] *)
Definition W_MISC_CAT_ID : Z := 0x0.
Definition AW_INTEROP_CAT_VPTR    : Z := 0x115a70.   (* [comment removed for export] *)
Definition W_INTEROP_CAT_ID : Z := 0xb2ab117a257edfd2.
Definition AW_GENERIC_CAT_VPTR    : Z := 0x1159b0.   (* [comment removed for export] *)
Definition W_GENERIC_CAT_ID : Z := 0xb2ab117a257edfd0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CAT_ID_SYSGEN_SHR1 : Z := 0x595588bd12bf6fe8.   (* [comment removed for export] *)
Definition ATI_NAME_CONFIG        : Z := 0x25280.   (* [comment removed for export] *)
Definition ATI_NAME_SCHED         : Z := 0x25994.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AL_STR_SCHEDULER           : Z := 0x25100.   (* [comment removed for export] *)
Definition AL_STR_REACTOR             : Z := 0x25200.   (* [comment removed for export] *)
Definition AL_STR_IO_LOCKING          : Z := 0x25220.   (* [comment removed for export] *)
Definition AL_STR_REG_LOCKING         : Z := 0x25240.   (* [comment removed for export] *)
Definition AL_STR_CONCURRENCY_HINT    : Z := 0x25120.   (* [comment removed for export] *)
Definition AL_STR_LOCKING             : Z := 0x251c0.   (* [comment removed for export] *)
Definition AL_STR_ONE                 : Z := 0x25160.   (* [comment removed for export] *)
Definition AL_STR_ZERO                : Z := 0x251e0.   (* [comment removed for export] *)
Definition AL_STR_MINUS_ONE           : Z := 0x25180.   (* [comment removed for export] *)
Definition AL_STR_FMT_D               : Z := 0x251a0.   (* [comment removed for export] *)
Definition AL_STR_ASSUME_CONT         : Z := 0x25d80.   (* [comment removed for export] *)
Definition AL_STR_SPIN                : Z := 0x25dc0.   (* [comment removed for export] *)
Definition AL_STR_TASK_USEC           : Z := 0x25e00.   (* [comment removed for export] *)
Definition AL_STR_WAIT_USEC           : Z := 0x25e20.   (* [comment removed for export] *)
Definition AL_EXECUTION_CONTEXT_PROP  : Z := 0x29220.   (* [comment removed for export] *)
Definition AL_TYPEID_CONFIG           : Z := 0x115d38.   (* [comment removed for export] *)
Definition AL_TYPEID_SCHED            : Z := 0x1162c0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition O_EC_VAL             : Z := 0x0.   (* [comment removed for export] *)
Definition O_EC_CAT             : Z := 0x8.   (* [comment removed for export] *)
Definition O_EC_FLAGS           : Z := 0x10.   (* [comment removed for export] *)
Definition SZ_EC                : Z := 0x18.
Definition O_FB_BEGIN           : Z := 0x0.
Definition O_FB_IN              : Z := 0x8.
Definition O_FB_OUT             : Z := 0x10.
Definition O_FB_LAST            : Z := 0x18.
Definition O_FB_END             : Z := 0x20.
Definition O_FB_MAX             : Z := 0x28.
Definition SZ_FB                : Z := 0x30.
Definition O_IOC_ALLOC          : Z := 0x0.   (* [comment removed for export] *)
Definition O_IOC_REGISTRY       : Z := 0x8.   (* [comment removed for export] *)
Definition O_IOC_IMPL           : Z := 0x10.   (* [comment removed for export] *)
Definition SZ_IOC               : Z := 0x18.
Definition SZ_ALLOCIMPL         : Z := 0x10.   (* [comment removed for export] *)
Definition O_REG_MUTEX          : Z := 0x8.   (* [comment removed for export] *)
Definition O_REG_OWNER          : Z := 0x30.   (* [comment removed for export] *)
Definition O_REG_FIRST          : Z := 0x38.   (* [comment removed for export] *)
Definition SZ_REG               : Z := 0x40.
Definition NEWSZ_REG            : Z := 0x4f.   (* [comment removed for export] *)
Definition O_SVC_VPTR           : Z := 0x0.
Definition O_SVC_KEY_TI         : Z := 0x8.   (* [comment removed for export] *)
Definition O_SVC_KEY_ID         : Z := 0x10.   (* [comment removed for export] *)
Definition O_SVC_OWNER          : Z := 0x18.   (* [comment removed for export] *)
Definition O_SVC_NEXT           : Z := 0x20.   (* [comment removed for export] *)
Definition O_SVC_DESTROY        : Z := 0x28.   (* [comment removed for export] *)
Definition SZ_SVC               : Z := 0x30.
Definition O_CFG_HINT           : Z := 0x30.   (* [comment removed for export] *)
Definition SZ_CFG               : Z := 0x38.
Definition NEWSZ_CFG            : Z := 0x47.
Definition O_SCH_ONE_THREAD     : Z := 0x30.   (* [comment removed for export] *)
Definition O_SCH_ASSUME_CONT    : Z := 0x31.   (* [comment removed for export] *)
Definition O_SCH_MUTEX          : Z := 0x38.   (* [comment removed for export] *)
Definition O_SCH_PMUTEX         : Z := 0x40.   (* [comment removed for export] *)
Definition O_SCH_SPIN           : Z := 0x68.   (* [comment removed for export] *)
Definition O_SCH_ENABLED        : Z := 0x6c.   (* [comment removed for export] *)
Definition O_SCH_EVENT          : Z := 0x70.   (* [comment removed for export] *)
Definition O_SCH_COND           : Z := 0x78.   (* [comment removed for export] *)
Definition O_SCH_EVSTATE        : Z := 0xa8.   (* [comment removed for export] *)
Definition O_SCH_TASK           : Z := 0xb0.   (* [comment removed for export] *)
Definition O_SCH_GET_TASK       : Z := 0xb8.   (* [comment removed for export] *)
Definition O_SCH_TASK_OP        : Z := 0xc0.   (* [comment removed for export] *)
Definition O_SCH_TASK_INTR      : Z := 0xd8.   (* [comment removed for export] *)
Definition O_SCH_STOPPED        : Z := 0xd9.   (* [comment removed for export] *)
Definition O_SCH_SHUTDOWN       : Z := 0xda.   (* [comment removed for export] *)
Definition O_SCH_OUTWORK        : Z := 0xe0.   (* [comment removed for export] *)
Definition O_SCH_OPQ            : Z := 0xe8.   (* [comment removed for export] *)
Definition O_SCH_TASK_USEC      : Z := 0xf8.   (* [comment removed for export] *)
Definition O_SCH_WAIT_USEC      : Z := 0x100.   (* [comment removed for export] *)
Definition O_SCH_THREAD         : Z := 0x108.   (* [comment removed for export] *)
Definition SZ_SCH               : Z := 0x110.
Definition NEWSZ_SCH            : Z := 0x11f.
Definition O_SSVC_SP_PX         : Z := 0x30.   (* [comment removed for export] *)
Definition O_SSVC_SP_PN         : Z := 0x38.   (* [comment removed for export] *)
Definition SZ_SSVC              : Z := 0x40.
Definition NEWSZ_SSVC           : Z := 0x4f.
Definition O_SPC_VPTR           : Z := 0x0.
Definition O_SPC_USE            : Z := 0x8.   (* [comment removed for export] *)
Definition O_SPC_WEAK           : Z := 0xc.   (* [comment removed for export] *)
Definition O_SPC_PTR            : Z := 0x10.   (* [comment removed for export] *)
Definition O_SPC_DEL_INIT       : Z := 0x18.   (* [comment removed for export] *)
Definition O_SPC_STORAGE        : Z := 0x20.   (* [comment removed for export] *)
Definition SZ_SPCI_IMPL         : Z := 0x60.   (* [comment removed for export] *)
Definition SZ_SPCI_STATE        : Z := 0x138.   (* [comment removed for export] *)
Definition O_IMPL_MUTEX         : Z := 0x0.   (* [comment removed for export] *)
Definition O_IMPL_VEC_BEGIN     : Z := 0x28.   (* [comment removed for export] *)
Definition O_IMPL_VEC_END       : Z := 0x30.   (* [comment removed for export] *)
Definition O_IMPL_VEC_CAP       : Z := 0x38.   (* [comment removed for export] *)
Definition SZ_IMPL              : Z := 0x40.
Definition O_ST_EXEC            : Z := 0x0.   (* [comment removed for export] *)
Definition O_ST_EXEC_OBJFNS     : Z := 0x18.
Definition O_ST_EXEC_TARGET     : Z := 0x20.
Definition O_ST_EXEC_TGTFNS     : Z := 0x28.
Definition O_ST_EXEC_PROPFNS    : Z := 0x30.
Definition O_ST_WP_PX           : Z := 0x38.   (* [comment removed for export] *)
Definition O_ST_WP_PN           : Z := 0x40.   (* [comment removed for export] *)
Definition O_ST_MUTEX           : Z := 0x48.   (* [comment removed for export] *)
Definition O_ST_FB              : Z := 0x70.   (* [comment removed for export] *)
Definition O_ST_CV              : Z := 0xa0.   (* [comment removed for export] *)
Definition O_ST_OP              : Z := 0xd0.   (* [comment removed for export] *)
Definition O_ST_CODE            : Z := 0xd8.   (* [comment removed for export] *)
Definition O_ST_FC              : Z := 0xe0.   (* [comment removed for export] *)
Definition O_ST_NREAD           : Z := 0xe8.
Definition O_ST_NREAD_BYTES     : Z := 0xf0.
Definition O_ST_NWRITE          : Z := 0xf8.
Definition O_ST_NWRITE_BYTES    : Z := 0x100.
Definition O_ST_READ_MAX        : Z := 0x108.   (* [comment removed for export] *)
Definition O_ST_WRITE_MAX       : Z := 0x110.   (* [comment removed for export] *)
Definition SZ_ST                : Z := 0x118.
Definition O_BS_IN_PX           : Z := 0x0.   (* [comment removed for export] *)
Definition O_BS_IN_PN           : Z := 0x8.   (* [comment removed for export] *)
Definition O_BS_OUT_PX          : Z := 0x10.   (* [comment removed for export] *)
Definition O_BS_OUT_PN          : Z := 0x18.   (* [comment removed for export] *)
Definition SZ_BS                : Z := 0x20.
Definition O_M_TYPE             : Z := 0x0.   (* [comment removed for export] *)
Definition O_M_LOCK             : Z := 0x4.   (* [comment removed for export] *)
Definition O_M_WAITERS          : Z := 0x8.   (* [comment removed for export] *)
Definition O_M_COUNT            : Z := 0x14.   (* [comment removed for export] *)
Definition O_M_PREV             : Z := 0x18.
Definition O_M_NEXT             : Z := 0x20.
Definition SZ_PMUTEX            : Z := 0x28.
Definition O_C_SHARED           : Z := 0x0.   (* [comment removed for export] *)
Definition O_C_HEAD             : Z := 0x8.   (* [comment removed for export] *)
Definition O_C_SEQ              : Z := 0x8.   (* [comment removed for export] *)
Definition O_C_WAITERS          : Z := 0xc.   (* [comment removed for export] *)
Definition O_C_CLOCK            : Z := 0x10.   (* [comment removed for export] *)
Definition O_C_LOCK             : Z := 0x20.   (* [comment removed for export] *)
Definition O_C_TAIL             : Z := 0x28.   (* [comment removed for export] *)
Definition SZ_PCOND             : Z := 0x30.
Definition O_EL_NEXT            : Z := 0x0.   (* [comment removed for export] *)
Definition O_EL_PREV            : Z := 0x8.   (* [comment removed for export] *)
Definition O_EL_PARENT          : Z := 0x10.   (* [comment removed for export] *)
Definition O_EL_LEFT            : Z := 0x18.
Definition O_EL_RIGHT           : Z := 0x20.
Definition O_EL_COLOR           : Z := 0x28.   (* [comment removed for export] *)
Definition O_EL_OFF             : Z := 0x30.   (* [comment removed for export] *)
Definition O_EL_LEN             : Z := 0x32.   (* [comment removed for export] *)
Definition O_EL_F               : Z := 0x34.   (* [comment removed for export] *)
Definition O_EL_TEXT            : Z := 0x38.   (* [comment removed for export] *)
Definition O_RBN_PARENT         : Z := 0x0.   (* [comment removed for export] *)
Definition O_RBN_LEFT           : Z := 0x8.
Definition O_RBN_RIGHT          : Z := 0x10.
Definition O_RBN_COLOR          : Z := 0x18.   (* [comment removed for export] *)
Definition SZ_RBN               : Z := 0x20.
Definition O_MBE_NEXT           : Z := 0x0.   (* [comment removed for export] *)
Definition O_MBE_PREV           : Z := 0x8.
Definition O_MBE_SIZE           : Z := 0x10.   (* [comment removed for export] *)
Definition O_MBE_DATA           : Z := 0x18.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition EBUSY                      : Z := 0x10.   (* [comment removed for export] *)
Definition ERANGE                     : Z := 0x22.
Definition EINVAL                     : Z := 0x16.
Definition CLOCK_MONOTONIC            : Z := 0x1.   (* [comment removed for export] *)
Definition STREAM_OK                  : Z := 0x0.   (* [comment removed for export] *)
Definition STREAM_EOF                 : Z := 0x1.   (* [comment removed for export] *)
Definition ASIO_ERR_EOF               : Z := 0x2.   (* [comment removed for export] *)
Definition ASIO_ERR_OPERATION_ABORTED : Z := 0x7d.   (* [comment removed for export] *)
Definition CONCURRENCY_HINT_DEFAULT   : Z := (-1).   (* [comment removed for export] *)
Definition HTTP_ERR_END_OF_STREAM     : Z := 0x1.   (* [comment removed for export] *)
Definition HTTP_ERR_PARTIAL_MESSAGE   : Z := 0x2.
Definition HTTP_ERR_NEED_MORE         : Z := 0x3.
Definition HTTP_ERR_BUFFER_OVERFLOW   : Z := 0x7.
Definition HTTP_ERR_HEADER_LIMIT      : Z := 0x8.
Definition HTTP_ERR_BODY_LIMIT        : Z := 0x9.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition le4z (z : Z) : list byte := le4 (wz z).
Definition u64max : Z := 2^64 - 1.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AErrCode (m : mem) (a : Z) (E : ecv) : Prop := rw_cells asegs m a (ErrCodeCells E) /\ ec_ok E.

(* [comment removed for export] *)
Definition EC_asio_eof : ecv := ec_make ASIO_ERR_EOF AG_MISC_CAT_INST.    (* [comment removed for export] *)

(* [comment removed for export] *)
Record fbv := mkFB { fb_begin : Z ; fb_in : Z ; fb_out : Z ; fb_last : Z ; fb_end : Z }.
Definition FB_empty : fbv := mkFB 0 0 0 0 0.
Definition FlatBufCells (F : fbv) : list cell :=
  [C8 (wz (fb_begin F)); C8 (wz (fb_in F)); C8 (wz (fb_out F)); C8 (wz (fb_last F)); C8 (wz (fb_end F)); C8 (wz u64max)].
Definition fb_size (F : fbv) : Z := fb_out F - fb_in F.
Definition fb_cap (F : fbv) : Z := fb_end F - fb_begin F.
(* [comment removed for export] *)
Definition fb_ok (LB : list block) (F : fbv) : Prop :=
  (F = FB_empty)
  \/ (exists p, In (p, fb_begin F, fb_cap F) LB /\ rblock_range (fb_begin F) (fb_cap F) /\ 0 < fb_cap F
      /\ fb_begin F <= fb_in F <= fb_out F /\ fb_out F <= fb_last F <= fb_end F).
Definition AFlatBuf (LB : list block) (m : mem) (a : Z) (F : fbv) (ds : list byte) : Prop :=
  rw_cells asegs m a (FlatBufCells F) /\ fb_ok LB F /\ zlength ds = fb_size F
  /\ (F <> FB_empty -> exists pre junk,
        rw_cells asegs m (fb_begin F) [CB (Z.to_nat (fb_in F - fb_begin F)) pre; CB (length ds) ds;
                                     CB (Z.to_nat (fb_end F - fb_out F)) junk])
  /\ (F <> FB_empty -> addressable m (fb_begin F) (fb_cap F)).                               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PMutexCells (lk : Z) : list cell := [CB 4 (zeros 4); C4 (wz lk); CB 32 (zeros 32)].
Definition APMutex (m : mem) (a : Z) (lk : Z) : Prop := rw_cells asegs m a (PMutexCells lk) /\ (lk = 0 \/ lk = EBUSY) /\ a mod 4 = 0.
(* [comment removed for export] *)
Definition PMutexZeroCells : list cell := [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
Definition PCondCells (clk : Z) : list cell := [CB 16 (zeros 16); C4 (wz clk); CB 12 (zeros 12); C4 (wz 0); CB 4 (zeros 4); C8 (wz 0)].
Definition APCond (m : mem) (a : Z) (clk : Z) : Prop := rw_cells asegs m a (PCondCells clk) /\ (clk = 0 \/ clk = CLOCK_MONOTONIC) /\ a mod 8 = 0.

(* [comment removed for export] *)
Record svch := mkSVC { sv_vptr : Z ; sv_ti : Z ; sv_id : Z ; sv_owner : Z ; sv_next : Z ; sv_destroy : Z }.
Definition SvcHdrCells (S : svch) : list cell :=
  [C8 (wz (sv_vptr S)); C8 (wz (sv_ti S)); C8 (wz (sv_id S)); C8 (wz (sv_owner S)); C8 (wz (sv_next S)); C8 (wz (sv_destroy S))].

(* [comment removed for export] *)
Definition CookieCells (junk7 : list byte) : list cell := [CB 8 (zeros 8); CB 7 junk7].

(* [comment removed for export] *)
Definition AAllocImpl (LB : list block) (m : mem) (a : Z) : Prop :=
  exists p junk, In (p, a, SZ_ALLOCIMPL) LB /\ rw_cells asegs m a [C8 (wz AVP_ALLOCIMPL); CB 8 junk]
  /\ rblock_range a SZ_ALLOCIMPL /\ addressable m a SZ_ALLOCIMPL.                            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ARegistry (LB : list block) (m : mem) (r : Z) (owner first lk : Z) : Prop :=
  exists p j0 j7, In (p, r, NEWSZ_REG) LB
  /\ rw_cells asegs m r [CB 8 j0]
  /\ APMutex m (r + O_REG_MUTEX) lk
  /\ rw_cells asegs m (r + O_REG_OWNER) [C8 (wz owner); C8 (wz first)]
  /\ rw_cells asegs m (r + SZ_REG) (CookieCells j7)
  /\ rblock_range r NEWSZ_REG /\ addressable m r NEWSZ_REG.                                  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AConfigSvc (LB : list block) (m : mem) (c : Z) (S : svch) : Prop :=
  exists p j4 j7, In (p, c, NEWSZ_CFG) LB
  /\ rw_cells asegs m c (SvcHdrCells S ++ [C4 (wz (2^32 - 1)); CB 4 j4] ++ CookieCells j7)
  /\ sv_vptr S = AVP_CONFIG_SVC /\ sv_destroy S = P_A_DESTROY_ALLOC_CONFIG
  /\ rblock_range c NEWSZ_CFG /\ addressable m c NEWSZ_CFG.                                  (* [comment removed for export] *)

(* [comment removed for export] *)
Record schv := mkSCH { sch_hdr : svch ; sch_lk : Z ; sch_stopped : Z ; sch_shutdown : Z }.
Definition AScheduler (LB : list block) (m : mem) (s : Z) (S : schv) : Prop :=
  exists p j50 jm j109 je jt j219 j7, In (p, s, NEWSZ_SCH) LB
  /\ rw_cells asegs m s (SvcHdrCells (sch_hdr S))
  /\ rw_cells asegs m (s + O_SCH_ONE_THREAD) [CB 2 [b8 0; b8 0]; CB 6 j50]           (* [comment removed for export] *)
  /\ rw_cells asegs m (s + O_SCH_MUTEX) [CB 8 jm]                                     (* [comment removed for export] *)
  /\ APMutex m (s + O_SCH_PMUTEX) (sch_lk S)                                            (* [comment removed for export] *)
  /\ rw_cells asegs m (s + O_SCH_SPIN) [C4 (wz 0); CB 1 [b8 1]; CB 3 j109]            (* [comment removed for export] *)
  /\ rw_cells asegs m (s + O_SCH_EVENT) [CB 8 je]                                     (* [comment removed for export] *)
  /\ APCond m (s + O_SCH_COND) CLOCK_MONOTONIC                                          (* [comment removed for export] *)
  /\ rw_cells asegs m (s + O_SCH_EVSTATE)
       [C8 (wz 0);                                   (* [comment removed for export] *)
        C8 (wz 0); C8 (wz P_A_SCHED_GET_DEFAULT_TASK); (* [comment removed for export] *)
        C8 (wz 0); C8 (wz 0); C4 (wz 0); CB 4 jt;    (* [comment removed for export] *)
        CB 3 [b8 1; b8 (sch_stopped S); b8 (sch_shutdown S)]; CB 5 j219;   (* [comment removed for export] *)
        C8 (wz 0);                                   (* [comment removed for export] *)
        C8 (wz 0); C8 (wz 0);                        (* [comment removed for export] *)
        C8 (wz u64max); C8 (wz u64max);              (* [comment removed for export] *)
        C8 (wz 0)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m (s + SZ_SCH) (CookieCells j7)
  /\ sv_vptr (sch_hdr S) = AVP_SCHED /\ sv_destroy (sch_hdr S) = P_A_DESTROY_ALLOC_SCHED
  /\ (sch_stopped S = 0 \/ sch_stopped S = 1) /\ (sch_shutdown S = 0 \/ sch_shutdown S = 1)
  /\ rblock_range s NEWSZ_SCH /\ addressable m s NEWSZ_SCH.                                  (* [comment removed for export] *)

(* [comment removed for export] *)
Record spcv := mkSPC { spc_vptr : Z ; spc_use : Z ; spc_weak : Z ; spc_init : Z }.
Definition SpcHdrCells (C : spcv) (j7 : list byte) : list cell :=
  [C8 (wz (spc_vptr C)); C4 (wz (spc_use C)); C4 (wz (spc_weak C)); C8 (wz 0); CB 1 [b8 (spc_init C)]; CB 7 j7].
Definition spc_ok (C : spcv) : Prop := 0 <= spc_use C < 2^31 /\ 0 <= spc_weak C < 2^31 /\ (spc_init C = 0 \/ spc_init C = 1).

(* [comment removed for export] *)
Record implv := mkIMPL { im_hdr : spcv ; im_lk : Z ; im_vb : Z ; im_states : list Z ; im_vcap : Z }.
Definition AImplBlock (LB : list block) (m : mem) (b : Z) (I : implv) : Prop :=
  exists p j7, In (p, b, SZ_SPCI_IMPL) LB /\ rblock_range b SZ_SPCI_IMPL
  /\ rw_cells asegs m b (SpcHdrCells (im_hdr I) j7) /\ spc_ok (im_hdr I) /\ spc_vptr (im_hdr I) = AVP_SPCI_IMPL
  /\ APMutex m (b + O_SPC_STORAGE + O_IMPL_MUTEX) (im_lk I)
  /\ rw_cells asegs m (b + O_SPC_STORAGE + O_IMPL_VEC_BEGIN)
       [C8 (wz (im_vb I)); C8 (wz (im_vb I + 8 * zlength (im_states I))); C8 (wz (im_vb I + 8 * im_vcap I))]
  /\ zlength (im_states I) <= im_vcap I
  /\ ((im_vcap I = 0 /\ im_vb I = 0)
      \/ (exists q junk, In (q, im_vb I, 8 * im_vcap I) LB /\ rblock_range (im_vb I) (8 * im_vcap I) /\ 0 < im_vcap I
           /\ rw_cells asegs m (im_vb I) [CB (8 * length (im_states I)) (flat_map le8z (im_states I));
                                         CB (Z.to_nat (8 * (im_vcap I - zlength (im_states I)))) junk]
           /\ addressable m (im_vb I) (8 * im_vcap I)))                                      (* [comment removed for export] *)
  /\ addressable m b SZ_SPCI_IMPL.                                                           (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AnyExecCells (a ioc : Z) (j16 : list byte) : list cell :=
  [C8 (wz ioc); CB 16 j16; C8 (wz AT_ANYEX_OBJECT_FNS); C8 (wz a); C8 (wz AT_ANYEX_TARGET_FNS); C8 (wz AT_ANYEX_PROP_FNS)].

(* [comment removed for export] *)
Record statev := mkST { st_hdr : spcv ; st_lk : Z ; st_fb : fbv ; st_code : Z ; st_nread : Z ; st_nread_bytes : Z }.
Definition AStateBlock (LB : list block) (m : mem) (b ioc implb : Z) (S : statev) (ds : list byte) : Prop :=
  exists p j7 j16 j4, In (p, b, SZ_SPCI_STATE) LB /\ rblock_range b SZ_SPCI_STATE
  /\ rw_cells asegs m b (SpcHdrCells (st_hdr S) j7) /\ spc_ok (st_hdr S) /\ spc_vptr (st_hdr S) = AVP_SPCI_STATE
  /\ rw_cells asegs m (b + 32 + O_ST_EXEC) (AnyExecCells (b + 32 + O_ST_EXEC) ioc j16)
  /\ rw_cells asegs m (b + 32 + O_ST_WP_PX) [C8 (wz (implb + O_SPC_STORAGE)); C8 (wz implb)]
  /\ APMutex m (b + 32 + O_ST_MUTEX) (st_lk S)
  /\ AFlatBuf LB m (b + 32 + O_ST_FB) (st_fb S) ds
  /\ APCond m (b + 32 + O_ST_CV) 0
  /\ rw_cells asegs m (b + 32 + O_ST_OP)
       [C8 (wz 0);                          (* [comment removed for export] *)
        C4 (wz (st_code S)); CB 4 j4;       (* [comment removed for export] *)
        C8 (wz 0);                          (* [comment removed for export] *)
        C8 (wz (st_nread S)); C8 (wz (st_nread_bytes S));
        C8 (wz 0); C8 (wz 0);               (* [comment removed for export] *)
        C8 (wz u64max); C8 (wz u64max)]     (* [comment removed for export] *)
  /\ (st_code S = STREAM_OK \/ st_code S = STREAM_EOF) /\ 0 <= st_nread S < 2^63 /\ 0 <= st_nread_bytes S < 2^63
  /\ addressable m b SZ_SPCI_STATE.                                                          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AStreamSvc (LB : list block) (m : mem) (v : Z) (S : svch) (implb : Z) : Prop :=
  exists p j7, In (p, v, NEWSZ_SSVC) LB
  /\ rw_cells asegs m v (SvcHdrCells S ++ [C8 (wz (implb + O_SPC_STORAGE)); C8 (wz implb)] ++ CookieCells j7)
  /\ sv_vptr S = AVP_SSVC /\ sv_destroy S = P_A_DESTROY_ALLOC_SSVC
  /\ rblock_range v NEWSZ_SSVC /\ addressable m v NEWSZ_SSVC.                                (* [comment removed for export] *)

(* [comment removed for export] *)
Definition BasicStreamCells (stateb : Z) : list cell :=
  [C8 (wz (stateb + O_SPC_STORAGE)); C8 (wz stateb); C8 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
Definition IoCtxCells (allocb regb schedb : Z) : list cell := [C8 (wz allocb); C8 (wz regb); C8 (wz schedb)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AIoWorld2 (LB : list block) (m : mem) (ioc allocb regb cfgb schedb : Z) : Prop :=
  rw_cells asegs m ioc (IoCtxCells allocb regb schedb)
  /\ AAllocImpl LB m allocb
  /\ ARegistry LB m regb ioc schedb 0
  /\ AConfigSvc LB m cfgb (mkSVC AVP_CONFIG_SVC AL_TYPEID_CONFIG 0 ioc 0 P_A_DESTROY_ALLOC_CONFIG)
  /\ AScheduler LB m schedb (mkSCH (mkSVC AVP_SCHED AL_TYPEID_SCHED 0 ioc cfgb P_A_DESTROY_ALLOC_SCHED) 0 0 0).
(* [comment removed for export] *)
Definition AImplBlockV (LB : list block) (m : mem) (implb : Z) (use weak : Z) (states : list Z) (vcap : Z) : Prop :=
  exists vb, AImplBlock LB m implb (mkIMPL (mkSPC AVP_SPCI_IMPL use weak 1) 0 vb states vcap).
(* [comment removed for export] *)
Definition AIoWorld3 (LB : list block) (m : mem) (ioc bs allocb regb cfgb schedb ssvcb implb stateb : Z)
           (F : fbv) (ds : list byte) (code nread nread_bytes : Z) : Prop :=
  rw_cells asegs m ioc (IoCtxCells allocb regb schedb)
  /\ rw_cells asegs m bs (BasicStreamCells stateb)
  /\ AAllocImpl LB m allocb
  /\ ARegistry LB m regb ioc ssvcb 0
  /\ AConfigSvc LB m cfgb (mkSVC AVP_CONFIG_SVC AL_TYPEID_CONFIG 0 ioc 0 P_A_DESTROY_ALLOC_CONFIG)
  /\ AScheduler LB m schedb (mkSCH (mkSVC AVP_SCHED AL_TYPEID_SCHED 0 ioc cfgb P_A_DESTROY_ALLOC_SCHED) 0 0 0)
  /\ AStreamSvc LB m ssvcb (mkSVC AVP_SSVC 0 AG_ID_SSVC ioc schedb P_A_DESTROY_ALLOC_SSVC) implb
  /\ AImplBlockV LB m implb 1 2 [stateb + O_SPC_STORAGE] 1
  /\ AStateBlock LB m stateb ioc implb (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 F code nread nread_bytes) ds.
(* [comment removed for export] *)
Definition AIoWorld4 (LB : list block) (m : mem) (ioc allocb regb cfgb schedb ssvcb implb : Z) : Prop :=
  rw_cells asegs m ioc (IoCtxCells allocb regb schedb)
  /\ AAllocImpl LB m allocb
  /\ ARegistry LB m regb ioc ssvcb 0
  /\ AConfigSvc LB m cfgb (mkSVC AVP_CONFIG_SVC AL_TYPEID_CONFIG 0 ioc 0 P_A_DESTROY_ALLOC_CONFIG)
  /\ AScheduler LB m schedb (mkSCH (mkSVC AVP_SCHED AL_TYPEID_SCHED 0 ioc cfgb P_A_DESTROY_ALLOC_SCHED) 0 0 0)
  /\ AStreamSvc LB m ssvcb (mkSVC AVP_SSVC 0 AG_ID_SSVC ioc schedb P_A_DESTROY_ALLOC_SSVC) implb
  /\ AImplBlockV LB m implb 1 1 [] 1.

(* [comment removed for export] *)
Lemma AErrCode_clear_intro : forall m a, rw_cells asegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> AErrCode m a EC_clear.
Proof. intros m a H. split; [exact H|]. unfold ec_ok, EC_clear; cbn; lia. Qed.
Lemma AFlatBuf_empty_intro : forall LB m a,
  rw_cells asegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz u64max)] -> AFlatBuf LB m a FB_empty [].
Proof.
  intros LB m a H. split; [exact H|]. split; [left; reflexivity|]. split; [reflexivity|].
  split; intros NE; exfalso; apply NE; reflexivity.
Qed.

End HCW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XS.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition AXStatics2 (m : mem) : Prop :=
     rw_cells asegs m AVP_ALLOCIMPL   (wcells [AVS_ALLOCIMPL_0; AVS_ALLOCIMPL_8; AVS_ALLOCIMPL_16; AVS_ALLOCIMPL_24; AVS_ALLOCIMPL_32])
  /\ rw_cells asegs m AVP_CONFIG_SVC  (wcells [AVS_CONFIG_SVC_0; AVS_CONFIG_SVC_8; AVS_CONFIG_SVC_16; AVS_CONFIG_SVC_24; AVS_CONFIG_SVC_32])
  /\ rw_cells asegs m AVP_SCHED       (wcells [AVS_SCHED_0; AVS_SCHED_8; AVS_SCHED_16; AVS_SCHED_24])
  /\ rw_cells asegs m AVP_SSVC        (wcells [AVS_SSVC_0; AVS_SSVC_8; AVS_SSVC_16; AVS_SSVC_24])
  /\ rw_cells asegs m AVP_SPCI_IMPL   (wcells [AVS_SPCI_IMPL_0; AVS_SPCI_IMPL_8; AVS_SPCI_IMPL_16; AVS_SPCI_IMPL_24; AVS_SPCI_IMPL_32; AVS_SPCI_IMPL_40; AVS_SPCI_IMPL_48])
  /\ rw_cells asegs m AVP_SPCI_STATE  (wcells [AVS_SPCI_STATE_0; AVS_SPCI_STATE_8; AVS_SPCI_STATE_16; AVS_SPCI_STATE_24; AVS_SPCI_STATE_32; AVS_SPCI_STATE_40; AVS_SPCI_STATE_48])
  /\ rw_cells asegs m AVP_PARSER      (wcells [AVS_PARSER_0; AVS_PARSER_8; AVS_PARSER_16; AVS_PARSER_24; AVS_PARSER_32; AVS_PARSER_40; AVS_PARSER_48; AVS_PARSER_56; AVS_PARSER_64; AVS_PARSER_72; AVS_PARSER_80; AVS_PARSER_88])
  /\ rw_cells asegs m AVP_HTTP_ECAT   (wcells [AVS_HTTP_ECAT_0; AVS_HTTP_ECAT_8; AVS_HTTP_ECAT_16; AVS_HTTP_ECAT_24; AVS_HTTP_ECAT_32; AVS_HTTP_ECAT_40; AVS_HTTP_ECAT_48])
  /\ rw_cells asegs m AT_ANYEX_OBJECT_FNS (wcells AT_ANYEX_OBJECT_FNS_words)
  /\ rw_cells asegs m AT_ANYEX_TARGET_FNS (wcells AT_ANYEX_TARGET_FNS_words)
  /\ rw_cells asegs m AT_ANYEX_PROP_FNS   (wcells AT_ANYEX_PROP_FNS_words)
  /\ rw_cells asegs m AT_ANYEX_PROP_FNS_VOID (wcells AT_ANYEX_PROP_FNS_VOID_words)
  /\ rw_cells asegs m (AL_TYPEID_CONFIG + 8) (wcells [ATI_NAME_CONFIG])
  /\ rw_cells asegs m (AL_TYPEID_SCHED + 8)  (wcells [ATI_NAME_SCHED])
  /\ rw_cells asegs m AG_SYSTEM_CAT_INST (wcells [AW_SYSTEM_CAT_VPTR; W_SYSTEM_CAT_ID])
  /\ rw_cells asegs m AG_MISC_CAT_INST   (wcells [AW_MISC_CAT_VPTR; W_MISC_CAT_ID]).

(* [comment removed for export] *)
Definition AXStatics2_ivs : list (Z * Z) :=
  [(AVP_ALLOCIMPL, AVP_ALLOCIMPL + 40); (AVP_CONFIG_SVC, AVP_CONFIG_SVC + 40); (AVP_SCHED, AVP_SCHED + 32); (AVP_SSVC, AVP_SSVC + 32);
   (AVP_SPCI_IMPL, AVP_SPCI_IMPL + 56); (AVP_SPCI_STATE, AVP_SPCI_STATE + 56); (AVP_PARSER, AVP_PARSER + 96); (AVP_HTTP_ECAT, AVP_HTTP_ECAT + 56);
   (AT_ANYEX_OBJECT_FNS, AT_ANYEX_OBJECT_FNS + 32); (AT_ANYEX_TARGET_FNS, AT_ANYEX_TARGET_FNS + 32);
   (AT_ANYEX_PROP_FNS, AT_ANYEX_PROP_FNS + 168); (AT_ANYEX_PROP_FNS_VOID, AT_ANYEX_PROP_FNS_VOID + 168);
   (AL_TYPEID_CONFIG + 8, AL_TYPEID_CONFIG + 16); (AL_TYPEID_SCHED + 8, AL_TYPEID_SCHED + 16);
   (AG_SYSTEM_CAT_INST, AG_SYSTEM_CAT_INST + 16); (AG_MISC_CAT_INST, AG_MISC_CAT_INST + 16)].
Scheme kc__1 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma AXStatics2_transport : forall W m m',
  AXStatics2 m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv : Z * Z => 0x125e40 <= fst iv \/ snd iv <= 0x115000) W ->
  AXStatics2 m'.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsIface.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.XS.AXStatics2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.I); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.Lists.List.Forall_inv); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.Lists.List.Forall_inv_tail); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVP_ALLOCIMPL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.wcells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_ALLOCIMPL_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_ALLOCIMPL_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_ALLOCIMPL_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_ALLOCIMPL_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_ALLOCIMPL_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVP_CONFIG_SVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_CONFIG_SVC_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_CONFIG_SVC_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_CONFIG_SVC_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_CONFIG_SVC_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_CONFIG_SVC_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVP_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SCHED_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SCHED_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SCHED_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SCHED_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVP_SSVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SSVC_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SSVC_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SSVC_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SSVC_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVP_SPCI_IMPL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_IMPL_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_IMPL_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_IMPL_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_IMPL_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_IMPL_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_IMPL_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_IMPL_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVP_SPCI_STATE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_STATE_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_STATE_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_STATE_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_STATE_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_STATE_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_STATE_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_SPCI_STATE_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVP_PARSER); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_56); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_72); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_80); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AVS_PARSER_88); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AVP_HTTP_ECAT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AVS_HTTP_ECAT_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AVS_HTTP_ECAT_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AVS_HTTP_ECAT_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AVS_HTTP_ECAT_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AVS_HTTP_ECAT_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AVS_HTTP_ECAT_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.AVS_HTTP_ECAT_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AT_ANYEX_OBJECT_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AT_ANYEX_OBJECT_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AT_ANYEX_TARGET_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AT_ANYEX_TARGET_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AT_ANYEX_PROP_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AT_ANYEX_PROP_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AT_ANYEX_PROP_FNS_VOID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AT_ANYEX_PROP_FNS_VOID_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AL_TYPEID_CONFIG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.ATI_NAME_CONFIG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AL_TYPEID_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.ATI_NAME_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AG_SYSTEM_CAT_INST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AW_SYSTEM_CAT_VPTR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.W_SYSTEM_CAT_ID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AG_MISC_CAT_INST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.AW_MISC_CAT_VPTR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.W_MISC_CAT_ID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@kc__1 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))|] [|@iv; @FW; @W; @l; @p; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__arith; @H1; @IH; @hi; @lo; @z; @a; @HA; @n; @A; @x; @y; @m; @H14; @H13; @H12; @H11; @H10; @H9; @H8; @H7; @H6; @H5; @H4; @H3; @H2; @H0; @H; @D; @WM; @MU; @XS; @m'|] "#?O#g%Q#u#x$<$=##$;%@%C%:%8%6$B$D%4%,${#$$$#z$s#a#d$k$f$a$[$T#-#)#,#.#b#*#1#5#9#=#A#E#I#M#Q#U#Y#]#g#f#e#%#0%G#4#&#2#8#6#<#:#@#>#D#B#H#k#(#F#L%R#'#J#P#N#T#R#X$.#V#\#p#Z#j#n#m#r#+$3$/$4$6$5$>$9$K$L#/#^#_#`#q#s#t#w#}#~$($,$7$8$:$E$H$N$M$O$P$I$Q$)$%$Z$Y$X$W$V$`$_$^$]$\$e$d$c$b$j$i$h$g$r$q$p$o$n$m$l$z$y$x$w$v$u$t%+%*%)%(%'%&%%%$%#$~$}$|%3%2%1%0%/%.%-%5%7%9%;%<%=%>%?%B%A%E%D#3#7#;#?#C#G#K#O#S#W#[#c%M%O%P#l$#$S$2#o$*#|$J$@$?#{$A$G$F$-$U%H%K%N%L%J%I%F$R$&%Q#v$1#y$0$C$'$+G%1%%2'%3$%4$#5%#4%%5&%6$%7%%8'%9*%:$%;%#U$%<&%=*%>'%?$%@$%A&%B5%C/%D)%E'$'&%F-%G(%H&%I/%J&%K%%L%%M&%N%%O$%P'UScSR&Sa&#&#&#&#&#USd#USe#USd(USe#USu#k##&#USfS#WSvSGSCS#WSwCSGSCVSxDD*1&#&#*#*#&#&#&#&#&#&#&#&#&#&#&#&#&#.#WSyDDG&Sa&#*#&#&#*#&#*#*#*#*#&#&#*#&#&#&#&#&#&#.#&6*#&#*#&#*#&#&#&#&#&#&#&#&#&#&#&#&#.#*0*#*#*#*#*#&#&#*#&#&#&#.#&.&#&#*#*#&#*#&#&#&#.#*s#*&#&#&#*#*#*#&#*#&#&#&#&#&#.#*1&#&#*#*#&#&#*#&#&#&#&#&#.#*,&#&#&#&#&#&#&#.#*+*#*#&#&#&#&#.#*s#.&#&#*#&#&#&#*#&#&#&#.#*-*#&#*#*#*#&#&#&#.#*s#6&#*#*#&#*#&#&#&#&#&#.#&-*#*#*#&#*#&#&#&#.#*5&#&#&#&#&#&#.#&4*#&#&#&#&#&#&#.#*s#x&#&#*#*#*#&#&#&#.#&s#s*#*#&#&#&#&#&#&#.#*s$O*#*#*#*#&#*#&#&#*#*#*#&#&#&#&#.#*-&#&#&#*#*#&#&#&#.#'s$ls%%WSzDDG*s%H&#*#&#*#&#&#&#&#&#&#&#&#&#&#&#&#.#'5s$mB7#j#$s%O#@s%P#SS's$qS#(S#G'#s%*#%#@s%U(G>S#SWSGk#%$#j#&s%h#ESR@s%Z-#j#%#S{>S#S/SSk#%*#)SRSCS#@s%_2#)SRSGSC>#S3S/k#%%#k##(#k#'s%t#j#(s%e#>S#S0Sgk#%4#FDDSGSC)SR#S#@s%j=#FDDSWSGYS|s%l?#SCGU@$(S1S.'#SS'SWS1B$#>SGS1S.%Sh%#%#%#AD#AD%ADShCD$#CD&#VSi#SjAD+AD-CD$#CD+#VSi#SjES^)S^$#)S^*#UScS^VSkDSWUS}DXSlD$SC#VSkDSGXSlD$S##US~DUT#D/Ds%d*SaDD#,D%N#-'HEEF#ODDs&D/Ds%W,D$N#-+HEEF#O[Sm,HEEF'#UT$EDDSa,D(N#-0HEEF#ODDs&N1D&#,D#N2-4HEEF#O25HEEF'#,D&N3-7HEEF#O,D2N,-9HEEF#O[Sm:HEEF%#\Sn;HEEF(0#\Sn<HEEF21#VT%=F+SoSpVT&GSCWT'So#Spm$%#WT(DT)S#XT*GSC$#l#)*)#l#*s#'s#&#l#+s#.s#-#j#,D#j#-D#j#.D#j#/D#'s&0SC'SGs%zB$#(S#SC'#s&4#s#k#(SCSG'#SW'SSSCB$#k##'#k##+#k#,D#k#-D#k#.D#k#/D#ZGSSS/S1SqS#S.l#04$#FDDSSSWYT+s&ls#{#SGS#USC#3s#[s#Z&#)SR&SG>#S1S.m#%#l#1s#ds#c#j#%s#g#j#2s#k#j#&s')#j#3D#j#4D#V#S#Gj#5D#j#5D#YT,DDs#t#Gj#6SR#ZT-SRs$'s$$#S0SGj#7s$,#j#8D#j#9D#>S0SCS#k##s$0#k#8D#k#9D#ED)DT.#)DT/#)DT0#)DT1#)DT2#4#$CS/S-#)DT3*)DT4#)DT5#)DT6#)DT7#4#$CS/S,#)DT81)DT9#)DT:#)DT;#4#$CS/S+#)DT<7)DT=#)DT>#)DT?#4#$CS/S*#)DT@=)DTA#)DTB#)DTC#)DTD#)DTE#)DTF#4#$CS/S)#)DTGs#&)DTH#)DTI#)DTJ#)DTK#)DTL#)DTM#4#$CS/S&#)DTNs#/)DTO#)DTP#)DTQ#)DTR#)DTS#)DTT#)DTU#)DTV#)DTW#)DTX#)DTY#4#$CS/R#)DTZs#=)DT[#)DT\#)DT]#)DT^#)DT_#)DT`#4#$CS/Q#4Ta$CS/P#4Tb$CS/M#4Tc$CS/L#4Td$CS/K#.s(&(Te#)DTfs#P4#$CS/%#(Tg')DThs#T4#$CS/%#)DTis#W)DTj#4#$CS/I#)DTks#[)DTl#4#$CS/J##'##,##1##7##:##=##@##s####s#-##s#<##s#F##s#P##s#W##s#^##s#f#j####$CS3S,s#b$CS3S+s#]$CS3S*s#X$CS3S)s#P$CS3S&s#H$CS3Rs#;$CS3Qs#3$CS3Ps#2$CS3Ms#1$CS3Ls#0$CS3Ks#/$CS3s#-s#+$CS3s#*s#($CS3Is#%$CS3JB#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CSgS-s$*$CS0S,s$$$CS0S+s#{$CS0S*s#v$CS0S)s#n$CS0S&s#f$CS0Rs#Y$CS0Qs#Q$CS0Ps#P$CS0Ms#O$CS0Ls#N$CS0Ks#M$CS0s#Ks#I$CS0s#Hs#F$CS0Is#C$CS0Js#@#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CS.S,s$A$CS.S+s$<$CS.S*s$7$CS.S)s$/$CS.S&s$'$CS.Rs#v$CS.Qs#n$CS.Ps#m$CS.Ms#l$CS.Ls#k$CS.Ks#j$CS.s#hs#f$CS.s#es#c$CS.Is#`$CS.Js#]#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CS.S-s$e##$j##%#$CS1S+s$[$CS1S*s$V$CS1S)s$N$CS1S&s$F$CS1Rs$9$CS1Qs$1$CS1Ps$0$CS1Ms$/$CS1Ls$.$CS1Ks$-$CS1s$+s$)$CS1s$(s$&$CS1Is$#$CS1Js#|#$##&##(##*##,##.##0##2##4##6##8##:##<#$CSqS,s$|$CSDS+s$w$CSDS*s$r$CSDS)s$j$CSDS&s$b$CSDRs$U$CSDQs$M$CSDPs$L$CSDMs$K$CSDLs$J$CSDKs$I$CSDs$Gs$E$CSDs$Ds$B$CSDIs$?$CSDJs$<#$##&##(##*##,##.##0##2##4##6##8##:##<#$CS4S+s%6$CS4S*s%1$CS4S)s%)$CS4S&s$}$CS4Rs$p$CS4Qs$h$CS4Ps$g$CS4Ms$f$CS4Ls$e$CS4Ks$d$CS4s$bs$`$CS4s$_s$]$CS4Is$Z$CS4Js$W#$##&##(##*##,##.##0##2##4##6##8##:##<#$CS4S-s%^$CS4S,s%X##%#%#j##'#$CSHS*s%P$CSHS)s%H$CSHS&s%@$CSHRs%3$CSHQs%+$CSHPs%*$CSHMs%)$CSHLs%($CSHKs%'$CSHs%%s%#$CSHs$~s$|$CSHIs$y$CSHJs$v#$##&##(##*##,##.##0##2##4##6##8##:#$CTmS+s%o$CSFS*s%j$CSFS)s%b$CSFS&s%Z$CSFRs%M$CSFQs%E$CSFPs%D$CSFMs%C$CSFLs%B$CSFKs%A$CSFs%?s%=$CSFs%<s%:$CSFIs%7$CSFJs%4#$##&##(##*##,##.##0##2##4##6##8##:#$CS5S*s&'$CS5S)s%{$CS5S&s%s$CS5Rs%f$CS5Qs%^$CS5Ps%]$CS5Ms%\$CS5Ls%[$CS5Ks%Z$CS5s%Xs%V$CS5s%Us%S$CS5Is%P$CS5Js%M#$##&##(##*##,##.##0##2##4##6##8##:#$CS5S-s&S$CS5S,s&M$CS5S+s&H##&#%##'#j##)#$CSJS)s&>$CSJS&s&6$CSJRs&)$CSJQs%}$CSJPs%|$CSJMs%{$CSJLs%z$CSJKs%y$CSJs%ws%u$CSJs%ts%r$CSJIs%o$CSJJs%l#$##&##(##*##,##.##0##2##4##6##8#$CTnS*s&^$CSIS)s&V$CSIS&s&N$CSIRs&A$CSIQs&9$CSIPs&8$CSIMs&7$CSILs&6$CSIKs&5$CSIs&3s&1$CSIs&0s&.$CSIIs&+$CSIJs&(#$##&##(##*##,##.##0##2##4##6##8#$CS6S)s&m$CS6S&s&e$CS6Rs&X$CS6Qs&P$CS6Ps&O$CS6Ms&N$CS6Ls&M$CS6Ks&L$CS6s&Js&H$CS6s&Gs&E$CS6Is&B$CS6Js&?#$##&##(##*##,##.##0##2##4##6##8#$CS6S-s'D$CS6S,s'>$CS6S+s'9$CS6S*s'4##'#%##'##)#j##+#$CSLS&s'($CSLRs&w$CSLQs&o$CSLPs&n$CSLMs&m$CSLLs&l$CSLKs&k$CSLs&is&g$CSLs&fs&d$CSLIs&a$CSLJs&^#$##&##(##*##,##.##0##2##4##6#$CToS)s'F$CSKS&s'>$CSKRs'1$CSKQs')$CSKPs'($CSKMs''$CSKLs'&$CSKKs'%$CSKs'#s&}$CSKs&|s&z$CSKIs&w$CSKJs&t#$##&##(##*##,##.##0##2##4##6#$CS7S&s'S$CS7Rs'F$CS7Qs'>$CS7Ps'=$CS7Ms'<$CS7Ls';$CS7Ks':$CS7s'8s'6$CS7s'5s'3$CS7Is'0$CS7Js'-#$##&##(##*##,##.##0##2##4##6#$CS7S-s(1$CS7S,s(+$CS7S+s(&$CS7S*s'}$CS7S)s'u##(#%##'##)##+#j##-#$CSNRs'e$CSNQs']$CSNPs'\$CSNMs'[$CSNLs'Z$CSNKs'Y$CSNs'Ws'U$CSNs'Ts'R$CSNIs'O$CSNJs'L#$##&##(##*##,##.##0##2##4#$CTpS&s(*$CSMRs'y$CSMQs'q$CSMPs'p$CSMMs'o$CSMLs'n$CSMKs'm$CSMs'ks'i$CSMs'hs'f$CSMIs'c$CSMJs'`#$##&##(##*##,##.##0##2##4#$CS8Rs(0$CS8Qs(($CS8Ps('$CS8Ms(&$CS8Ls(%$CS8Ks($$CS8s'~s'|$CS8s'{s'y$CS8Is'v$CS8Js's#$##&##(##*##,##.##0##2##4#$CS8S-s(v$CS8S,s(p$CS8S+s(k$CS8S*s(f$CS8S)s(^$CS8S&s(V##)#%##'##)##+##-#j##/#$CSPQs(G$CSPPs(F$CSPMs(E$CSPLs(D$CSPKs(C$CSPs(As(?$CSPs(>s(<$CSPIs(9$CSPJs(6#$##&##(##*##,##.##0##2#$CTqRs(a$CSOQs(Y$CSOPs(X$CSOMs(W$CSOLs(V$CSOKs(U$CSOs(Ss(Q$CSOs(Ps(N$CSOIs(K$CSOJs(H#$##&##(##*##,##.##0##2#$CS9Qs(j$CS9Ps(i$CS9Ms(h$CS9Ls(g$CS9Ks(f$CS9s(ds(b$CS9s(as(_$CS9Is(\$CS9Js(Y#$##&##(##*##,##.##0##2#$CS9S-s)[$CS9S,s)U$CS9S+s)P$CS9S*s)K$CS9S)s)C$CS9S&s);$CS9Rs).##*#%##'##)##+##-##/#j##1#$CSTPs),$CSTMs)+$CSTLs)*$CSTKs))$CSTs)'s)%$CSTs)$s(~$CSTIs({$CSTJs(x#$##&##(##*##,##.##0#$CTrQs)=$CSQPs)<$CSQMs);$CSQLs):$CSQKs)9$CSQs)7s)5$CSQs)4s)2$CSQIs)/$CSQJs),#$##&##(##*##,##.##0#$CS:Ps)K$CS:Ms)J$CS:Ls)I$CS:Ks)H$CS:s)Fs)D$CS:s)Cs)A$CS:Is)>$CS:Js);#$##&##(##*##,##.##0#$CS:S-s*<$CS:S,s*6$CS:S+s*1$CS:S*s*,$CS:S)s*$$CS:S&s)x$CS:Rs)k$CS:Qs)c##+#%##'##)##+##-##/##1#j##3#$CSXMs)i$CSXLs)h$CSXKs)g$CSXs)es)c$CSXs)bs)`$CSXIs)]$CSXJs)Z#$##&##(##*##,##.#$CTsPs)x$CSUMs)w$CSULs)v$CSUKs)u$CSUs)ss)q$CSUs)ps)n$CSUIs)k$CSUJs)h#$##&##(##*##,##.#$CS;Ms*($CS;Ls*'$CS;Ks*&$CS;s*$s)~$CS;s)}s){$CS;Is)x$CS;Js)u#$##&##(##*##,##.#$CS;S-s*u$CS;S,s*o$CS;S+s*j$CS;S*s*e$CS;S)s*]$CS;S&s*U$CS;Rs*H$CS;Qs*@$CS;Ps*?##,#%##'##)##+##-##/##1##3#j##5#$CSZLs*F$CSZKs*E$CSZs*Cs*A$CSZs*@s*>$CSZIs*;$CSZJs*8#$##&##(##*##,#$CTtMs*S$CSYLs*R$CSYKs*Q$CSYs*Os*M$CSYs*Ls*J$CSYIs*G$CSYJs*D#$##&##(##*##,#$CS<Ls*]$CS<Ks*\$CS<s*Zs*X$CS<s*Ws*U$CS<Is*R$CS<Js*O#$##&##(##*##,#$CS<S-s+N$CS<S,s+H$CS<S+s+C$CS<S*s+>$CS<S)s+6$CS<S&s+.$CS<Rs*}$CS<Qs*u$CS<Ps*t$CS<Ms*s##-#%##'##)##+##-##/##1##3##5#j##7#$CS\Ks*{$CS\s*ys*w$CS\s*vs*t$CS\Is*q$CS\Js*n#$##&##(##*#$CTuLs+*$CS[Ks+)$CS[s+'s+%$CS[s+$s*~$CS[Is*{$CS[Js*x#$##&##(##*#$CS=Ks+2$CS=s+0s+.$CS=s+-s++$CS=Is+($CS=Js+%#$##&##(##*#$CS=S-s,#$CS=S,s+y$CS=S+s+t$CS=S*s+o$CS=S)s+g$CS=S&s+_$CS=Rs+R$CS=Qs+J$CS=Ps+I$CS=Ms+H$CS=Ls+G##.#%##'##)##+##-##/##1##3##5##7#j##9#$CS_s+Os+M$CS_s+Ls+J$CS_Is+G$CS_Js+D#$##&##(#$CTvKs+Y$CS]s+Ws+U$CS]s+Ts+R$CS]Is+O$CS]Js+L#$##&##(#$CS>s+^s+\$CS>s+[s+Y$CS>Is+V$CS>Js+S#$##&##(#$CS>S-s,P$CS>S,s,J$CS>S+s,E$CS>S*s,@$CS>S)s,8$CS>S&s,0$CS>Rs,#$CS>Qs+w$CS>Ps+v$CS>Ms+u$CS>Ls+t$CS>Ks+s##/#%##'##)##+##-##/##1##3##5##7##9#j##;#$CSbs+zs+x$CSbIs+u$CSbJs+r#$##&#$CTws,'s,%$CS`s,$s+~$CS`Is+{$CS`Js+x#$##&#$CS?s,)s,'$CS?Is,$$CS?Js+}#$##&#$CS?S-s,y$CS?S,s,s$CS?S+s,n$CS?S*s,i$CS?S)s,a$CS?S&s,Y$CS?Rs,L$CS?Qs,D$CS?Ps,C$CS?Ms,B$CS?Ls,A$CS?Ks,@$CS?s,>s,<##0#%##'##)##+##-##/##1##3##5##7##9##;#j##=#$CSrIs,C$CSrJs,@#$#$CSss,Ls,J$CStIs,G$CStJs,D#$#$CS'Is,J$CS'Js,G#$#$CS'S-s-B$CS'S,s-<$CS'S+s-7$CS'S*s-2$CS'S)s-*$CS'S&s,~$CS'Rs,q$CS'Qs,i$CS'Ps,h$CS'Ms,g$CS'Ls,f$CS'Ks,e$CS's,cs,a$CS's,`s,^##1#%##'##)##+##-##/##1##3##5##7##9##;##=#j##?#$CS2Js,f$CTxIs,k$CS(Js,h$CS(S-s-b$CS(S,s-\$CS(S+s-W$CS(S*s-R$CS(S)s-J$CS(S&s-B$CS(Rs-5$CS(Qs--$CS(Ps-,$CS(Ms-+$CS(Ls-*$CS(Ks-)$CS(s-'s-%$CS(s-$s,~$CS(Is,{##2#%##'##)##+##-##/##1##3##5##7##9##;##=#5s.#0#*s/s&#&#&#&#*#&#*#*#&#*#&#&#&#.#'s2%s1t%s/J%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#(s2>#'#s2_#s#*#*s3=&#&#&#.#(s2F#'#s2g#s#2#+S@s#36s#4s#4#j#:DG'S#GUTy#j#;D#j#:D#XTzDDT{s0I+D#j#<D#j#8D#+Ds2T0G+D#j#:SV#+D5?SVDDDSESE00$?6#7DDDDDDS$111S$)s2Zs2Z(?7#+Ds2{8DDS%3S%/@8$s2|s2|#9s#G@s#G85#/Ds2^,Ds/sN#-s/{HEEF#O/D>1D&#,D#Ns/}-s0#HEEF#O2s0$HEEF'#l#)#s/fs/`l#*s0+s0'#l#+s01s0.#l#0#s##G:s#,s#$/#m##s#-'s2yS-(S-s#2'#s32#%#m#'#(S-s#k'#s36#)#m#&#;S-s#o#<CSASBS(S-s/6S`S2S'#5s/00#*s1)*#*#&#&#&#&#&#*#&#&#&#.#'s37s2{(s2|s#L'#s3L#%#(s3#s#G'#s3O#(#+S@)6**#+Ds3(7DDDDDDS$s#Gs#Gs#GS$s#?s3)s3)#s#Us#Ms#98DDS%s#HS%s#D,)#s3Us3Us#89.,.)&#/Ds3,,Ds0LN#-s0THEEF#O1D%s#7,D#Ns0U-s0WHEEF#O2s0XHEEF&#l#)#s0>s08l#*s0_s0[#l#+s0es0b#l#0#3G:74.#m##8's3QS,(S,s#f'#s3f#%#m#'#(S,s#/'#s3j#)#m#&#;S,s#3#<CSASBS(S,s/cS]S2S'#5s/^0#*s$H&#*#&#*#&#&#&#&#&#&#.#'s3js3C0s$,(s3E#'#s4$#&#.s4Z(s3I#'#s4(#*#+S@+6,,#+Ds3N+D)?SVDDDSESEs#}s#}s#qs$8*#7DDDDDDS$s#~s#~s#~S$s#vs3Qs3Q%/+#8DDS%s$#S%s#{/+#s40s40s#o92/2+(#/Ds3T,Ds1'N#-s1/HEEF#O/D11D&#,D#Ns11-s13HEEF#O2s14HEEF'#l#)#s0vs0pl#*s1;s17#l#+s1As1>#l#0#6G:;7/#m##<'s4-S+(S+A'#s4B#%#m#'#(S+s#3'#s4F#)#m#&#;S+s#7#<CSASBS(S+s09S[S2S'#5s040#*s%&&#*#&#&#*#*#&#&#&#&#&#&#.#'s4Hs3o(s3ps#<'#s4]#%#(s3ss#;'#s4`#(#+S@)6**#+Ds3x7DDDDDDS$s$Xs$Xs$XS$s$Ps3ys3y#s#Es#As#98DDS%s$YS%s$U,)#s4fs4fs$I9.,.)&#/Ds3|,Ds1]N#-s1eHEEF#O1D%s#8,D#Ns1f-s1hHEEF#O2s1iHEEF&#l#)#s1Os1Il#*s1ps1l#l#+s1vs1s#l#0#3G:74.#m##8's4bS*(S*s#V'#s4w#%#m#'#(S*s#0'#s4{#)#m#&#;S*s#4#<CSASBS(S*s0hSYS2S'#5s0`0#*s#4&#&#*#&#&#&#&#&#.#'s4ys4;%s%3%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#(s4M#'#s5C#6#*s2>&#&#&#.#(s4U#'#s5K#>#+S@?6@@#+Ds4Z+D)?SVDDDSESEs%Ds%Ds%83*#7DDDDDDS$s%Es%Es%ES$s%=s4]s4]%3+#8DDS%s%FS%s%B3+#s5Ss5Ss%69s#&3s#&+(#/Ds4`,Ds2JN#-s2RHEEF#O/D11D&#,D#Ns2T-s2VHEEF#O2s2WHEEF'#l#)#s2=s27l#*s2^s2Z#l#+s2ds2a#l#0#6G:?7/#m##@'s5PS)(S)s#%'#s5e#%#m#'#(S)s#E'#s5i#)#m#&#;S)s#I#<CSASBS(S)s1MSUS2S'#5s1E0#*s#L&#&#*#&#&#&#&#.#'s5fs4|(s4}s#;'#s5{#%#(s5$s#6'#s5~#(#+S@)6**#+Ds5)7DDDDDDS$s%vs%vs%vS$s%ns5*s5*#s#Ds#<s#48DDS%s%wS%s%s,)#s6(s6(s%g9.,.)&#/Ds5-,Ds2{N#-s3'HEEF#O1D%s#3,D#Ns3(-s3*HEEF#O2s3+HEEF&#l#)#s2ms2gl#*s32s3.#l#+s38s35#l#0#3G:74.#m##8's6$S&(S&s#U'#s69#%#m#'#(S&s#+'#s6=#)#m#&#;S&s#/#<CSASBS(S&s1tSQS2S'#5s1g0#*s%1&#&#&#*#&#*#&#&#&#.#'s6<s5F%s#n%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#(s5p#'#s6z#s#.#&s3u&#&#&#&#.#(s5y#'#s7'#s#7#+S@s#86s#9s#9#+Ds5~+D)?SVDDDSESEs&|s&|s&p4*#7DDDDDDS$s&}s&}s&}S$s&us6%s6%%4+#8DDS%s&~S%s&z4+#s7/s7/s&n9s#?4s#?+(#/Ds6(,Ds4&N#-s4.HEEF#O/D11D&#,D#Ns40-s42HEEF#O2s43HEEF'#l#)#s3us3ol#*s4:s46#l#+s4@s4=#l#0#6G:@7/#m##A's7,R(Rs#&'#s7A#%#m#'#(Rs#_'#s7E#)#m#&#;Rs#c#<CSASBS(Rs2nSOS2S'#5s2f0#*s#f&#*#&#*#*#&#&#&#.#'s7Cs6C(s6Ds$t'#s7X#%#(s6Gs$o'#s7[#(#+S@)6**#+Ds6L7DDDDDDS$s'Ss'Ss'SS$s'Ks6Ms6M#s$}s$us$m8DDS%s'TS%s'P,)#s7as7as'D9.,.)&#/Ds6P,Ds4XN#-s4`HEEF#O1D%s$l,D#Ns4a-s4cHEEF#O2s4dHEEF&#l#)#s4Js4Dl#*s4ks4g#l#+s4qs4n#l#0#3G:74.#m##8's7]Q(Qs%2'#s7r#%#m#'#(Qs#,'#s7v#)#m#&#;Qs#0#<CSASBS(Qs3:SMS2S'#5s390#*s&0*#&#*#&#&#&#&#&#&#.#'s7us6i(s6js&i'#s8.#%#(s6ms&h'#s81#(#+S@)6**#+Ds6r7DDDDDDS$s()s()s()S$s'}s6ss6s#s&rs&ns&f8DDS%s(*S%s(&,)#s87s87s'v9.,.)&#/Ds6v,Ds5.N#-s56HEEF#O1D%s&e,D#Ns57-s59HEEF#O2s5:HEEF&#l#)#s4|s4vl#*s5As5=#l#+s5Gs5D#l#0#3G:74.#m##8's83P(Ps'''#s8H#%#m#'#(Ps#-'#s8L#)#m#&#;Ps#1#<CSASBS(Ps3jSKS2S'#5s3i0#&s#4*#&#&#&#*#&#&#&#.#'s8Js74(s75s'>'#s8_#%#(s78s'='#s8b#(#+S@)6**#+Ds7=7DDDDDDS$s(Zs(Zs(ZS$s(Rs7>s7>#s'Gs'Cs';8DDS%s([S%s(W,)#s8hs8hs(K9.,.)&#/Ds7A,Ds5_N#-s5gHEEF#O1D%s':,D#Ns5h-s5jHEEF#O2s5kHEEF&#l#)#s5Qs5Kl#*s5rs5n#l#+s5xs5u#l#0#3G:74.#m##8's8dM(Ms'X'#s8y#%#m#'#(Ms#,'#s8}#)#m#&#;Ms#0#<CSASBS(Ms4=SIS2S'#5s4<0#*s#b&#&#&#&#&#.#'s8xs7Z%s$s%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#(s8H#'#s9z#s#N#*s)x&#&#&#.#(s8P#'#s:&#s#V#+S@s#W6s#Xs#X#+Ds8U+D)?SVDDDSESEs){s){s)o3*#7DDDDDDS$s)|s)|s)|S$s)ts8Xs8X%3+#8DDS%s)}S%s)y3+#s:.s:.s)m9s#^3s#^+(#/Ds8[,Ds7%N#-s7-HEEF#O/D11D&#,D#Ns7/-s71HEEF#O2s72HEEF'#l#)#s6ts6nl#*s79s75#l#+s7?s7<#l#0#6G:?7/#m##@'s:+L(Ls#%'#s:@#%#m#'#(Ls#z'#s:D#)#m#&#;Ls#~#<CSASBS(Ls5^SFS2S'#5s5]0#*s'9*#&#&#&#&#&#.#'s:@s8u(s8vs#:'#s:U#%#(s8ys#5'#s:X#(#+S@)6**#+Ds8~7DDDDDDS$s*Ps*Ps*PS$s*Hs9#s9##s#Cs#;s#38DDS%s*QS%s*M,)#s:^s:^s*A9.,.)&#/Ds9&,Ds7UN#-s7]HEEF#O1D%s#2,D#Ns7^-s7`HEEF#O2s7aHEEF&#l#)#s7Gs7Al#*s7hs7d#l#+s7ns7k#l#0#3G:74.#m##8's:ZK(Ks#T'#s:o#%#m#'#(Ks#*'#s:s#)#m#&#;Ks#.#<CSASBS(Ks6/SDS2S'#5s6+0#*s*<*#&#*#*#&#&#&#.#(s9?s69's:q#0s+K(%#'#s;+#&#((s6?'#s;.#)#+S@*6++#+D-+Ds6E?SVDDDSESEs+'s+'s*ws+Vs6F#7DDDDDDS$s+(s+(s+(S$s*|00%.s6G#8DDS%s+)S%s+%.+#s;6s;6s*u91.1+(#/Ds9P/Ds6K1D$#,Ds8/N#-s87HEEF#O1D%&,D#Ns88-s8:HEEF#O2s8;HEEF&#l#)#s7}s7wl#*s8Bs8>#l#+s8Hs8E#l#0#7G:;80#m##<'s;4s6X(s6YA'#s;I#%#m#'#(s6]s#1'#s;M#)#m#&#;s6as#5#<CSASBS(s6bs6`S0S2S'#5s6]0#&s*@&#*#*#&#&#&#&#&#.#(s9ls6p's;L#($s#9'#s;a#%#('s6u'#s;d#(#+S@)6**#+D,7DDDDDDS$s+\s+\s+\S$s+T--#s#Bs6{s#78DDS%s+]S%s+Y,)#s;js;js+M9.,.)&#/Ds9z1D#s#6,Ds8bN#-s8jHEEF#O1D%s#9,D#Ns8k-s8mHEEF#O2s8nHEEF&#l#)#s8Ts8Nl#*s8us8q#l#+s8{s8x#l#0#4G:85/#m##9's;gs7+(s7,s#T'#s;|#%#m#'#(s70s#.'#s<$#)#m#&#;s74s#2#<CSASBS(s75s73SSS2S'#5s700#*s9w*#*#*#*#*#&#&#&#&#&#*#&#&#&#&#.#'s<)s:90s,W(s:;#'#s<?#&#.s<v(s:?#'#s<C#*#+S@+6,,#+Ds:D+D)?SVDDDSESEs,<s,<s,0s,c*#7DDDDDDS$s,=s,=s,=S$s,5s:Gs:G%/+#8DDS%s,>S%s,:/+#s<Ks<Ks,.92/2+(#/Ds:J,Ds9BN#-s9JHEEF#O/D11D&#,D#Ns9L-s9NHEEF#O2s9OHEEF'#l#)#s95s9/l#*s9Vs9R#l#+s9\s9Y#l#0#6G:;7/#m##<'s<HI(IA'#s<]#%#m#'#(Is#8'#s<a#)#m#&#;Is#<#<CSASBS(Is7lS#S2S'#5s7i0#*s#8&#*#*#*#&#&#&#.#'s<^s:d(s:es#7'#s<s#%#(s:hs#6'#s<v#(#+S@)6**#+Ds:m7DDDDDDS$s,ns,ns,nS$s,fs:ns:n#s#@s#<s#48DDS%s,oS%s,k,)#s<|s<|s,_9.,.)&#/Ds:q,Ds9sN#-s9{HEEF#O1D%s#3,D#Ns9|-s9~HEEF#O2s:#HEEF&#l#)#s9es9_l#*s:*s:&#l#+s:0s:-#l#0#3G:74.#m##8's<xJ(Js#Q'#s=1#%#m#'#(Js#+'#s=5#)#m#&#;Js#/#<CSASBS(Js8<GS2S'#3s.$s.3s#3#3s.&s.$s#q#3s.(s.$s$I#3s.*s.$s%$#3s.,s.$s%T#3s..s.$s&x#3s.0s.$s'N#3s.2s.$s(%#3s.4s.$s(W#3s.6s.$s)`#3s.8s.$s*5#3s.:s.$s+$#3s.<s.$s+Z#3s.>s.$s,7#3s.@s.$s,l#j#=s.B#j#>s.D#V#S#Gj##s.G#j##s.h#=s.is.hs.J#Gj#>s.k#j#?s.o#V#S#Gj##s.r#j##s/9#=s/:s/7s.w#Gj#?s/<#j#@s/B#V#S#Gj##s/E#j##s/j#=s/ks/fs/L#Gj#@s/m#j#As/u#V#S#Gj##s/x#j##s0C#=s0Ds0=s0%#Gj#As0F#j#Bs0P#V#S#Gj##s0S#j##s0|#=s0}s0ts0^#Gj#Bs1##j#Cs1/#V#S#Gj##s12#j##s1]#=s1^s1Ss1?#Gj#Cs1`#j#Ds1n#V#S#Gj##s1q#j##s2B#=s2Cs26s2$#Gj#Ds2E#j#Es2U#V#S#Gj##s2X#j##s3+#=s3,s2ys2i#Gj#Es3.#j#Fs3@#V#S#Gj##s3C#j##s3t#=s3us3ds3V#Gj#Fs3w#j#Gs4/#V#S#Gj##s42#j##s4e#=s4fs4Ss4G#Gj#Gs4h#j#Hs4~#V#S#Gj##s5%#j##s5Z#=s5[s5Fs5<#Gj#Hs5]#j#Is5u#V#S#Gj##s5x#j##s6S#=s6Ts6=s65#Gj#Is6V#j#1s6p#V#S#Gj##s6s#j##s7P#=s7Qs78s72#Gj#1s7S#j#Js7o#V#S#Gj##s7r#j##s8Q#=s8Rs87s83#Gj#Js8T#j#Ks8r#V#S#Gj##s8u#j##s:@#=s:As9:s98#SWUSfSSm#$#l#Ls:Ps:L#j#%s<%#j#Ms>u#j#Ns>w#j#Os>y#j#Ps>{#j#<T|#j#&s?-##"). Qed.

(* [comment removed for export] *)
Definition AXStatics2_img_ok : bool :=
  forallb (fun ac : Z * list Z =>
             match image_bytes asegs (fst ac) (8 * length (snd ac))%nat with
             | Some bs => if list_eq_dec (fun a b : byte => @base.decide (a = b) (bv_eq_dec 8 a b)) bs (flat_map le8z (snd ac)) then true else false
             | None => false end)
    [(AVP_ALLOCIMPL, [AVS_ALLOCIMPL_0; AVS_ALLOCIMPL_8; AVS_ALLOCIMPL_16; AVS_ALLOCIMPL_24; AVS_ALLOCIMPL_32]);
     (AVP_CONFIG_SVC, [AVS_CONFIG_SVC_0; AVS_CONFIG_SVC_8; AVS_CONFIG_SVC_16; AVS_CONFIG_SVC_24; AVS_CONFIG_SVC_32]);
     (AVP_SCHED, [AVS_SCHED_0; AVS_SCHED_8; AVS_SCHED_16; AVS_SCHED_24]);
     (AVP_SSVC, [AVS_SSVC_0; AVS_SSVC_8; AVS_SSVC_16; AVS_SSVC_24]);
     (AVP_SPCI_IMPL, [AVS_SPCI_IMPL_0; AVS_SPCI_IMPL_8; AVS_SPCI_IMPL_16; AVS_SPCI_IMPL_24; AVS_SPCI_IMPL_32; AVS_SPCI_IMPL_40; AVS_SPCI_IMPL_48]);
     (AVP_SPCI_STATE, [AVS_SPCI_STATE_0; AVS_SPCI_STATE_8; AVS_SPCI_STATE_16; AVS_SPCI_STATE_24; AVS_SPCI_STATE_32; AVS_SPCI_STATE_40; AVS_SPCI_STATE_48]);
     (AVP_PARSER, [AVS_PARSER_0; AVS_PARSER_8; AVS_PARSER_16; AVS_PARSER_24; AVS_PARSER_32; AVS_PARSER_40; AVS_PARSER_48; AVS_PARSER_56; AVS_PARSER_64; AVS_PARSER_72; AVS_PARSER_80; AVS_PARSER_88]);
     (AVP_HTTP_ECAT, [AVS_HTTP_ECAT_0; AVS_HTTP_ECAT_8; AVS_HTTP_ECAT_16; AVS_HTTP_ECAT_24; AVS_HTTP_ECAT_32; AVS_HTTP_ECAT_40; AVS_HTTP_ECAT_48]);
     (AT_ANYEX_OBJECT_FNS, AT_ANYEX_OBJECT_FNS_words); (AT_ANYEX_TARGET_FNS, AT_ANYEX_TARGET_FNS_words);
     (AT_ANYEX_PROP_FNS, AT_ANYEX_PROP_FNS_words); (AT_ANYEX_PROP_FNS_VOID, AT_ANYEX_PROP_FNS_VOID_words);
     (AL_TYPEID_CONFIG + 8, [ATI_NAME_CONFIG]); (AL_TYPEID_SCHED + 8, [ATI_NAME_SCHED]);
     (AG_SYSTEM_CAT_INST, [AW_SYSTEM_CAT_VPTR; W_SYSTEM_CAT_ID]); (AG_MISC_CAT_INST, [AW_MISC_CAT_VPTR; W_MISC_CAT_ID])].
Lemma AXStatics2_img_ok_true : AXStatics2_img_ok = true.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep2.XS.AXStatics2_img_ok)|] Array.empty "##&###(#'#(#&#)#*#VECDWFCGDm$$##"). Qed.

(* [comment removed for export] *)
Lemma AXStatics2_AXStatics : forall m, AXStatics2 m -> AXStatics m.
Proof. intros m XS. unfold AXStatics2 in XS. destruct XS as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ACanaryReads (m : mem) : Prop :=
  Lib.PropExec.rdn asegs m (Z_to_bv 64 AG_GOT_STACK_CHK) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 AG_STACK_CHK_GUARD))
  /\ exists can : Z, Lib.PropExec.rdn asegs m (Z_to_bv 64 AG_STACK_CHK_GUARD) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).

End XS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RBL.
  Context {HCEIL : HeapCeil}.

Record rbnode := mkRBN { rbn_parent : Z ; rbn_left : Z ; rbn_right : Z ; rbn_color : Z }.
Definition RBnodeCells (n : rbnode) (pad : list byte) : list cell :=
  [C8 (wz (rbn_parent n)); C8 (wz (rbn_left n)); C8 (wz (rbn_right n)); C4 (wz (rbn_color n)); CB 4 pad].
Definition ARBcells (m : mem) (ns : gmap Z rbnode) : Prop :=
  map_Forall (fun (a : Z) (n : rbnode) => exists pad, rw_cells asegs m a (RBnodeCells n pad)) ns.

Record dlnode := mkDLN { dl_next : Z ; dl_prev : Z }.
Definition DLnodeCells (n : dlnode) : list cell := [C8 (wz (dl_next n)); C8 (wz (dl_prev n))].
Definition ADLcells (m : mem) (ls : gmap Z dlnode) : Prop :=
  map_Forall (fun (a : Z) (n : dlnode) => rw_cells asegs m a (DLnodeCells n)) ls.

(* [comment removed for export] *)
Definition ElemValueCells (f : Z) (name value : list byte) (tail : list byte) : list cell :=
  [C2 (wz (zlength name + 2)); C2 (wz (zlength value)); C2 (wz f); CB 2 [b8 0; b8 0];
   CB (length name) name; CB 2 [b8 58; b8 32]; CB (length value) value; CB 2 [b8 13; b8 10]; CB (length tail) tail].
(* [comment removed for export] *)
Definition elem_block_size (name value : list byte) : Z := Z.land (zlength name + 2 + zlength value + 65) (-8).

(* [comment removed for export] *)
Definition MBElemCells (next prev size : Z) (data junk : list byte) : list cell :=
  [C8 (wz next); C8 (wz prev); C8 (wz size); CB (length data) data; CB (length junk) junk].
Definition mb_block_size (size : Z) : Z := Z.land (size + 31) (-8).

(* [comment removed for export] *)
Lemma ARBcells_lookup : forall m ns a n, ARBcells m ns -> ns !! a = Some n -> exists pad, rw_cells asegs m a (RBnodeCells n pad).
Proof. intros m ns a n H L. exact (map_Forall_lookup_1 _ _ _ _ H L). Qed.
Lemma ADLcells_lookup : forall m ls a n, ADLcells m ls -> ls !! a = Some n -> rw_cells asegs m a (DLnodeCells n).
Proof. intros m ls a n H L. exact (map_Forall_lookup_1 _ _ _ _ H L). Qed.

End RBL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KIT.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma rw_cells_recells : forall m A cs cs',
  rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[WF B] W] WF' EB ES. split; [split|].
  - exact WF'.
  - rewrite EB. exact B.
  - rewrite ES. exact W.
Qed.

(* [comment removed for export] *)
Lemma APMutex_of_zero : forall m a, rw_cells asegs m a PMutexZeroCells -> a mod 4 = 0 -> APMutex m a 0.
Proof.
  intros m a H Ha. split; [| split; [left; reflexivity| exact Ha]].
  eapply rw_cells_recells; [exact H | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.
Lemma APCond_of_zero6 : forall m a, rw_cells asegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> a mod 8 = 0 -> APCond m a 0.
Proof.
  intros m a H Ha. split; [| split; [left; reflexivity| exact Ha]].
  eapply rw_cells_recells; [exact H | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma le8_firstn4 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Lemma C8_read_low4 : forall m A (w : word) cs,
  rw_cells asegs m A (C8 w :: cs) -> ov_read_bytes asegs m (wa A) 4 = Some (le4 w).
Proof.
  intros m A w cs [[WF B] _].
  pose proof (bytes_at_ov_read asegs m A _ 0 4 B) as R. rewrite Z.add_0_r in R.
  rewrite R. 2:{ cbn [cells_bytes cbytes app length]. rewrite length_app, length_le8. lia. }
  cbn [cells_bytes cbytes]. rewrite skipn_O, firstn_app, length_le8. cbn [Nat.sub firstn]. rewrite app_nil_r. rewrite le8_firstn4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma disjoint_from_sub : forall W a n a' n',
  disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros a n a' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; eauto].
Qed.

Ltac xtransport MU WM D :=
  eapply rw_cells_transport; [eassumption | exact MU | exact WM | eapply disjoint_from_sub; [exact D | cbn; lia | cbn; lia] ].

Lemma APMutex_transport : forall W m m' a lk,
  APMutex m a lk -> munch W m m' -> wmono asegs m m' -> disjoint_from W a SZ_PMUTEX -> APMutex m' a lk.
Proof.
  intros W m m' a lk (C & L & A) MU WM D. split; [| split; assumption].
  unfold PMutexCells, zeros, SZ_PMUTEX in *. xtransport MU WM D.
Qed.

Lemma APCond_transport : forall W m m' a clk,
  APCond m a clk -> munch W m m' -> wmono asegs m m' -> disjoint_from W a SZ_PCOND -> APCond m' a clk.
Proof.
  intros W m m' a clk (C & L & A) MU WM D. split; [| split; assumption].
  unfold PCondCells, zeros, SZ_PCOND in *. xtransport MU WM D.
Qed.

Lemma AErrCode_transport : forall W m m' a E,
  AErrCode m a E -> munch W m m' -> wmono asegs m m' -> disjoint_from W a SZ_EC -> AErrCode m' a E.
Proof.
  intros W m m' a E (C & OK) MU WM D. split; [| exact OK]. unfold ErrCodeCells, SZ_EC in *. xtransport MU WM D.
Qed.

Lemma AFlatBuf_transport : forall W LB m m' a F ds,
  AFlatBuf LB m a F ds -> munch W m m' -> wmono asegs m m' -> disjoint_from W a SZ_FB ->
  (F <> FB_empty -> disjoint_from W (fb_begin F) (fb_cap F)) ->
  (F <> FB_empty -> disjoint_from W (sh (fb_begin F)) (nsh (fb_cap F))) -> AFlatBuf LB m' a F ds.
Proof.
  intros W LB m m' a F ds (C & OK & L & DATA & AD) MU WM D DB DS. split; [| split; [exact OK| split; [exact L| split]]].
  - unfold FlatBufCells, SZ_FB in *. xtransport MU WM D.
  - intros NE. destruct (DATA NE) as (pre & junk & CD). exists pre, junk.
    destruct OK as [E|(p & IN & RB & CAP & O1 & O2)]; [contradiction|].
    pose proof (rw_cells_bound _ _ _ _ CD) as B. cbn [cells_size csize Nat.add] in B.
    destruct CD as [[WF BA] WR]. cbn in WF.
    eapply rw_cells_transport; [ split; [split; [exact WF| exact BA] | exact WR] | exact MU | exact WM |].
    eapply disjoint_from_sub; [exact (DB NE) | lia |].
    cbn [cells_size csize Nat.add]. unfold fb_cap, fb_size, zlength in *. lia.
  - intros NE. eapply addressable_transport; [exact (AD NE)| exact MU| exact WM| exact (DS NE)].
Qed.

Lemma AAllocImpl_transport : forall W LB m m' a,
  AAllocImpl LB m a -> munch W m m' -> wmono asegs m m' -> disjoint_from W a SZ_ALLOCIMPL ->
  disjoint_from W (sh a) (nsh SZ_ALLOCIMPL) -> AAllocImpl LB m' a.
Proof.
  intros W LB m m' a (p & junk & IN & C & RB & AD) MU WM D DS. exists p, junk. split; [exact IN|].
  split; [| split; [exact RB| eapply addressable_transport; [exact AD| exact MU| exact WM| exact DS]]].
  unfold SZ_ALLOCIMPL in *. xtransport MU WM D.
Qed.

Lemma ARegistry_transport : forall W LB m m' r owner first lk,
  ARegistry LB m r owner first lk -> munch W m m' -> wmono asegs m m' -> disjoint_from W r NEWSZ_REG ->
  disjoint_from W (sh r) (nsh NEWSZ_REG) -> ARegistry LB m' r owner first lk.
Proof.
  intros W LB m m' r owner first lk (p & j0 & j7 & IN & C0 & PM & C1 & C2 & RB & AD) MU WM D DS. exists p, j0, j7.
  assert (AD' : addressable m' r NEWSZ_REG) by (eapply addressable_transport; [exact AD| exact MU| exact WM| exact DS]).
  clear AD DS. unfold NEWSZ_REG, O_REG_MUTEX, O_REG_OWNER, SZ_REG, CookieCells, zeros in *.
  split; [exact IN|]. split; [xtransport MU WM D|]. split.
  { eapply APMutex_transport; [exact PM| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PMUTEX; lia]]. }
  split; [xtransport MU WM D|]. split; [xtransport MU WM D|]. split; [exact RB| exact AD'].
Qed.

Lemma AConfigSvc_transport : forall W LB m m' c S,
  AConfigSvc LB m c S -> munch W m m' -> wmono asegs m m' -> disjoint_from W c NEWSZ_CFG ->
  disjoint_from W (sh c) (nsh NEWSZ_CFG) -> AConfigSvc LB m' c S.
Proof.
  intros W LB m m' c S (p & j4 & j7 & IN & C & E1 & E2 & RB & AD) MU WM D DS. exists p, j4, j7. split; [exact IN|].
  assert (AD' : addressable m' c NEWSZ_CFG) by (eapply addressable_transport; [exact AD| exact MU| exact WM| exact DS]).
  clear AD DS. split; [| split; [exact E1| split; [exact E2| split; [exact RB| exact AD']]]].
  unfold NEWSZ_CFG, SvcHdrCells, CookieCells, zeros in *. xtransport MU WM D.
Qed.

Lemma AStreamSvc_transport : forall W LB m m' v S implb,
  AStreamSvc LB m v S implb -> munch W m m' -> wmono asegs m m' -> disjoint_from W v NEWSZ_SSVC ->
  disjoint_from W (sh v) (nsh NEWSZ_SSVC) -> AStreamSvc LB m' v S implb.
Proof.
  intros W LB m m' v S implb (p & j7 & IN & C & E1 & E2 & RB & AD) MU WM D DS. exists p, j7. split; [exact IN|].
  assert (AD' : addressable m' v NEWSZ_SSVC) by (eapply addressable_transport; [exact AD| exact MU| exact WM| exact DS]).
  clear AD DS. split; [| split; [exact E1| split; [exact E2| split; [exact RB| exact AD']]]].
  unfold NEWSZ_SSVC, SvcHdrCells, CookieCells, zeros in *. xtransport MU WM D.
Qed.

Lemma AScheduler_transport : forall W LB m m' s S,
  AScheduler LB m s S -> munch W m m' -> wmono asegs m m' -> disjoint_from W s NEWSZ_SCH ->
  disjoint_from W (sh s) (nsh NEWSZ_SCH) -> AScheduler LB m' s S.
Proof.
  intros W LB m m' s S (p & j50 & jm & j109 & je & jt & j219 & j7 & IN & C0 & C1 & C2 & PM & C3 & C4 & PC & C5 & C6 & E1 & E2 & E3 & E4 & RB & AD) MU WM D DS.
  assert (AD' : addressable m' s NEWSZ_SCH) by (eapply addressable_transport; [exact AD| exact MU| exact WM| exact DS]).
  clear AD DS. assert (E : sv_vptr (sch_hdr S) = AVP_SCHED /\ sv_destroy (sch_hdr S) = P_A_DESTROY_ALLOC_SCHED
    /\ (sch_stopped S = 0 \/ sch_stopped S = 1) /\ (sch_shutdown S = 0 \/ sch_shutdown S = 1)
    /\ rblock_range s NEWSZ_SCH /\ addressable m' s NEWSZ_SCH)
    by (split; [exact E1| split; [exact E2| split; [exact E3| split; [exact E4| split; [exact RB| exact AD']]]]]).
  clear E1 E2 E3 E4 RB AD'.
  exists p, j50, jm, j109, je, jt, j219, j7.
  unfold NEWSZ_SCH, SZ_SCH, O_SCH_ONE_THREAD, O_SCH_MUTEX, O_SCH_PMUTEX, O_SCH_SPIN, O_SCH_EVENT, O_SCH_COND, O_SCH_EVSTATE,
         SvcHdrCells, CookieCells, zeros in *.
  split; [exact IN|]. split; [xtransport MU WM D|]. split; [xtransport MU WM D|]. split; [xtransport MU WM D|].
  split. { eapply APMutex_transport; [exact PM| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PMUTEX; lia]]. }
  split; [xtransport MU WM D|]. split; [xtransport MU WM D|].
  split. { eapply APCond_transport; [exact PC| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PCOND; lia]]. }
  split; [xtransport MU WM D|]. split; [xtransport MU WM D| exact E].
Qed.

Lemma AImplBlock_transport : forall W LB m m' b I,
  AImplBlock LB m b I -> munch W m m' -> wmono asegs m m' -> disjoint_from W b SZ_SPCI_IMPL ->
  (0 < im_vcap I -> disjoint_from W (im_vb I) (8 * im_vcap I)) ->
  disjoint_from W (sh b) (nsh SZ_SPCI_IMPL) ->
  (0 < im_vcap I -> disjoint_from W (sh (im_vb I)) (nsh (8 * im_vcap I))) -> AImplBlock LB m' b I.
Proof.
  intros W LB m m' b I (p & j7 & IN & RB & CH & OK & EV & PM & CV & LE & ST & AD) MU WM D DV DS DSV. exists p, j7.
  assert (AD' : addressable m' b SZ_SPCI_IMPL) by (eapply addressable_transport; [exact AD| exact MU| exact WM| exact DS]).
  clear AD DS.
  unfold SZ_SPCI_IMPL, O_SPC_STORAGE, O_IMPL_MUTEX, O_IMPL_VEC_BEGIN, SpcHdrCells in *.
  split; [exact IN|]. split; [exact RB|]. split; [xtransport MU WM D|]. split; [exact OK|]. split; [exact EV|].
  split. { eapply APMutex_transport; [exact PM| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PMUTEX; lia]]. }
  split; [xtransport MU WM D|]. split; [exact LE|]. split; [| exact AD'].
  destruct ST as [ST|(q & junk & INq & RBq & POS & CS & ADq)]; [left; exact ST| right]. exists q, junk.
  split; [exact INq|]. split; [exact RBq|]. split; [exact POS|].
  split; [| eapply addressable_transport; [exact ADq| exact MU| exact WM| exact (DSV POS)]].
  pose proof (rw_cells_bound _ _ _ _ CS) as B. destruct CS as [[WF BA] WR].
  eapply rw_cells_transport; [ split; [split; [exact WF| exact BA] | exact WR] | exact MU | exact WM |].
  eapply disjoint_from_sub; [exact (DV POS) | lia |].
  cbn [cells_size csize Nat.add] in *. cbn in WF. unfold zlength in *. lia.
Qed.

Lemma AStateBlock_transport : forall W LB m m' b ioc implb S ds,
  AStateBlock LB m b ioc implb S ds -> munch W m m' -> wmono asegs m m' -> disjoint_from W b SZ_SPCI_STATE ->
  (st_fb S <> FB_empty -> disjoint_from W (fb_begin (st_fb S)) (fb_cap (st_fb S))) ->
  disjoint_from W (sh b) (nsh SZ_SPCI_STATE) ->
  (st_fb S <> FB_empty -> disjoint_from W (sh (fb_begin (st_fb S))) (nsh (fb_cap (st_fb S)))) -> AStateBlock LB m' b ioc implb S ds.
Proof.
  intros W LB m m' b ioc implb S ds (p & j7 & j16 & j4 & IN & RB & CH & OK & EV & CE & CW & PM & FB & PC & CO & E1 & E2 & E3 & AD) MU WM D DF DS DSF.
  assert (AD' : addressable m' b SZ_SPCI_STATE) by (eapply addressable_transport; [exact AD| exact MU| exact WM| exact DS]).
  clear AD DS. assert (E : (st_code S = STREAM_OK \/ st_code S = STREAM_EOF) /\ 0 <= st_nread S < 2^63 /\ 0 <= st_nread_bytes S < 2^63
    /\ addressable m' b SZ_SPCI_STATE)
    by (split; [exact E1| split; [exact E2| split; [exact E3| exact AD']]]).
  clear E1 E2 E3 AD'.
  exists p, j7, j16, j4.
  unfold SZ_SPCI_STATE, O_ST_EXEC, O_ST_WP_PX, O_ST_MUTEX, O_ST_FB, O_ST_CV, O_ST_OP, SpcHdrCells, AnyExecCells in *.
  split; [exact IN|]. split; [exact RB|]. split; [xtransport MU WM D|]. split; [exact OK|]. split; [exact EV|].
  split; [xtransport MU WM D|]. split; [xtransport MU WM D|].
  split. { eapply APMutex_transport; [exact PM| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PMUTEX; lia]]. }
  split. { eapply AFlatBuf_transport; [exact FB| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_FB; lia]| exact DF| exact DSF]. }
  split. { eapply APCond_transport; [exact PC| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PCOND; lia]]. }
  split; [xtransport MU WM D| exact E].
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_4_congr : forall a b, a mod 2^32 = b mod 2^32 -> Z_to_le_bytes 4 a = Z_to_le_bytes 4 b.
Proof.
  intros a b E. rewrite <- (Z_to_le_bytes_mod 4 a 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 b 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.

Lemma amo_add32_store : forall (v : word) (s : bv 32),
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 v))) s))
  = Z_to_le_bytes 4 ((bv_unsigned v + bv_unsigned s) mod 2^32).
Proof.
  intros v s. unfold amo_val. rewrite bv_add_unsigned.
  rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
  apply Z_to_le_bytes_4_congr.
  unfold bv_wrap. change (bv_modulus 32) with (2^32). change (2 ^ Z.of_N 32) with (2^32).
  rewrite !Z.mod_mod by lia. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma amo_old32 : forall v : word, sext 64 (bv_extract 0 32 (le_bytes_to_word (le4 v))) = sx32 v.
Proof. exact sext_extract_le4. Qed.

End KIT.

