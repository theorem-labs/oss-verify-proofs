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
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_FUZZ                       : Z := 0x2b3e0.   (* [comment removed for export] *)
Definition P_STREAM_CTOR                : Z := 0x2b6bc.   (* [comment removed for export] *)
Definition P_STREAM_CLOSE_REMOTE        : Z := 0x2b824.   (* [comment removed for export] *)
Definition P_PARSER_DTOR                : Z := 0x2b900.   (* [comment removed for export] *)
Definition P_STREAM_DTOR                : Z := 0x2b9cc.   (* [comment removed for export] *)
Definition P_ECAT_FAILED                : Z := 0x2bc80.   (* [comment removed for export] *)
Definition P_MAKE_SVC_CONFIG            : Z := 0x2c05c.   (* [comment removed for export] *)
Definition P_DESTROY_ALLOC_CONFIG       : Z := 0x2c128.   (* [comment removed for export] *)
Definition P_CONFIG_SHUTDOWN            : Z := 0x2c15c.   (* [comment removed for export] *)
Definition P_CONFIG_GET_VALUE           : Z := 0x2c164.   (* [comment removed for export] *)
Definition P_DEALLOC_OBJ_CONFIG         : Z := 0x2c324.   (* [comment removed for export] *)
Definition P_DO_ADD_SERVICE             : Z := 0x2c380.   (* [comment removed for export] *)
Definition P_THROW_INVALID_SERVICE_OWNER : Z := 0x2c4d8.   (* [comment removed for export] *)
Definition P_THROW_SERVICE_ALREADY_EXISTS : Z := 0x2c52c.   (* [comment removed for export] *)
Definition P_DESTROY_ADDED              : Z := 0x2c580.   (* [comment removed for export] *)
Definition P_STD_THROW_BAD_ARRAY_NEW_LENGTH : Z := 0x2cfc4.   (* [comment removed for export] *)
Definition P_ALLOCIMPL_DESTROY          : Z := 0x2cff8.   (* [comment removed for export] *)
Definition P_ALLOCIMPL_ALLOCATE         : Z := 0x2d030.   (* [comment removed for export] *)
Definition P_ALLOCIMPL_DEALLOCATE       : Z := 0x2d108.   (* [comment removed for export] *)
Definition P_ALLOCIMPL_BASE_DTOR        : Z := 0x2d17c.   (* [comment removed for export] *)
Definition P_THROW_BAD_ALLOC            : Z := 0x2d188.   (* [comment removed for export] *)
Definition P_ALLOC_OBJ_REGISTRY         : Z := 0x2d584.   (* [comment removed for export] *)
Definition P_THROW_SYSTEM_ERROR         : Z := 0x2d8f0.   (* [comment removed for export] *)
Definition P_MAKE_SVC_SCHED             : Z := 0x2e284.   (* [comment removed for export] *)
Definition P_ALLOC_OBJ_SCHED            : Z := 0x2e314.   (* [comment removed for export] *)
Definition P_DESTROY_ALLOC_SCHED        : Z := 0x2e3c0.   (* [comment removed for export] *)
Definition P_SCHED_GET_DEFAULT_TASK     : Z := 0x2e3ec.   (* [comment removed for export] *)
Definition P_SCHED_CTOR                 : Z := 0x2e42c.   (* [comment removed for export] *)
Definition P_DO_USE_SERVICE             : Z := 0x2e770.   (* [comment removed for export] *)
Definition P_CREATE_CONFIG              : Z := 0x2f854.   (* [comment removed for export] *)
Definition P_CONFIG_GET_BOOL            : Z := 0x2f93c.   (* [comment removed for export] *)
Definition P_THROW_OUT_OF_RANGE         : Z := 0x2f9f8.   (* [comment removed for export] *)
Definition P_CONFIG_GET_INT             : Z := 0x2fe70.   (* [comment removed for export] *)
Definition P_OPQUEUE_DTOR               : Z := 0x30738.   (* [comment removed for export] *)
Definition P_CEM_SCOPED_LOCK            : Z := 0x307a0.   (* [comment removed for export] *)
Definition P_CEM_CTOR                   : Z := 0x30a30.   (* [comment removed for export] *)
Definition P_SCHED_DTOR                 : Z := 0x30b70.   (* [comment removed for export] *)
Definition P_SCHED_DELDTOR              : Z := 0x30c9c.   (* [comment removed for export] *)
Definition P_SCHED_SHUTDOWN             : Z := 0x30cc8.   (* [comment removed for export] *)
Definition P_POSIX_EVENT_CTOR           : Z := 0x30e18.   (* [comment removed for export] *)
Definition P_CONFIG_GET_LONG            : Z := 0x30f30.   (* [comment removed for export] *)
Definition P_POSIX_EVENT_SIGNAL_ALL     : Z := 0x316a4.   (* [comment removed for export] *)
Definition P_DEALLOC_OBJ_SCHED          : Z := 0x31ca8.   (* [comment removed for export] *)
Definition P_DEALLOC_OBJ_REGISTRY       : Z := 0x31d04.   (* [comment removed for export] *)
Definition P_PARSER_DTOR_THUNK          : Z := 0x31d5c.   (* [comment removed for export] *)
Definition P_ON_REQUEST_IMPL            : Z := 0x31d88.   (* [comment removed for export] *)
Definition P_ON_RESPONSE_IMPL           : Z := 0x31da4.   (* [comment removed for export] *)
Definition P_ON_FIELD_IMPL              : Z := 0x31da8.   (* [comment removed for export] *)
Definition P_ON_TRAILER_FIELD_IMPL      : Z := 0x31db0.   (* [comment removed for export] *)
Definition P_ON_HEADER_IMPL             : Z := 0x31ed8.   (* [comment removed for export] *)
Definition P_ON_BODY_INIT_IMPL          : Z := 0x31ee8.   (* [comment removed for export] *)
Definition P_ON_BODY_IMPL               : Z := 0x31f00.   (* [comment removed for export] *)
Definition P_ON_CHUNK_HEADER_IMPL       : Z := 0x31f2c.   (* [comment removed for export] *)
Definition P_ON_CHUNK_BODY_IMPL         : Z := 0x31f40.   (* [comment removed for export] *)
Definition P_ON_FINISH_IMPL             : Z := 0x31f7c.   (* [comment removed for export] *)
Definition P_FIELDS_DTOR                : Z := 0x31f8c.   (* [comment removed for export] *)
Definition P_MB_DTOR                    : Z := 0x31fdc.   (* [comment removed for export] *)
Definition P_FIELDS_DELETE_LIST         : Z := 0x3202c.   (* [comment removed for export] *)
Definition P_FIELDS_REALLOC_STRING      : Z := 0x32084.   (* [comment removed for export] *)
Definition P_SV_COPY                    : Z := 0x32120.   (* [comment removed for export] *)
Definition P_ON_REQUEST_IMPL_T          : Z := 0x322e4.   (* [comment removed for export] *)
Definition P_EC_CTOR_HTTP               : Z := 0x323cc.   (* [comment removed for export] *)
Definition P_HEADER_SET_METHOD          : Z := 0x324b8.   (* [comment removed for export] *)
Definition P_HEADER_SET_VERSION         : Z := 0x32554.   (* [comment removed for export] *)
Definition P_FIELDS_REALLOC_TARGET      : Z := 0x326f8.   (* [comment removed for export] *)
Definition P_STRING_TO_VERB             : Z := 0x32c40.   (* [comment removed for export] *)
Definition P_SV_INDEX                   : Z := 0x333fc.   (* [comment removed for export] *)
Definition P_SV_REMOVE_PREFIX           : Z := 0x33444.   (* [comment removed for export] *)
Definition P_FIELDS_INSERT              : Z := 0x33498.   (* [comment removed for export] *)
Definition P_FIELDS_NEW_ELEMENT         : Z := 0x3350c.   (* [comment removed for export] *)
Definition P_FIELDS_INSERT_ELEMENT      : Z := 0x336bc.   (* [comment removed for export] *)
Definition P_FIELDS_VALUE_TYPE_CTOR     : Z := 0x338b8.   (* [comment removed for export] *)
Definition P_LIST_ITERATOR_TO           : Z := 0x33974.   (* [comment removed for export] *)
Definition P_RB_UPPER_BOUND_LOOP        : Z := 0x339b8.   (* [comment removed for export] *)
Definition P_KEY_COMPARE_SV_VT          : Z := 0x33a40.   (* [comment removed for export] *)
Definition P_FIELDS_FIND_SV             : Z := 0x33ac0.   (* [comment removed for export] *)
Definition P_LIST_ITERATOR_TO_C         : Z := 0x33b30.   (* [comment removed for export] *)
Definition P_RB_FIND                    : Z := 0x33b74.   (* [comment removed for export] *)
Definition P_RB_LOWER_BOUND_LOOP        : Z := 0x33bfc.   (* [comment removed for export] *)
Definition P_KEY_COMPARE_VT_SV          : Z := 0x33c7c.   (* [comment removed for export] *)
Definition P_RB_INSERT_BEFORE           : Z := 0x33cfc.   (* [comment removed for export] *)
Definition P_RB_REBALANCE               : Z := 0x33d94.   (* [comment removed for export] *)
Definition P_RB_INSERT_COMMIT           : Z := 0x33ec0.   (* [comment removed for export] *)
Definition P_RB_PREV_NODE               : Z := 0x33f48.   (* [comment removed for export] *)
Definition P_RB_IS_HEADER               : Z := 0x33fa4.   (* [comment removed for export] *)
Definition P_FIELDS_INDEX_F             : Z := 0x33fe4.   (* [comment removed for export] *)
Definition P_TOKEN_LIST_EXISTS          : Z := 0x34060.   (* [comment removed for export] *)
Definition P_FIELDS_FIND_F              : Z := 0x341b8.   (* [comment removed for export] *)
Definition P_FIELD_TABLE_CTOR           : Z := 0x342b8.   (* [comment removed for export] *)
Definition P_FIELD_TABLE_DIGEST         : Z := 0x343c0.   (* [comment removed for export] *)
Definition P_TOKEN_LIST_ITER_INCR       : Z := 0x34454.   (* [comment removed for export] *)
Definition P_TOKEN_LIST_ITER_CTOR       : Z := 0x34518.   (* [comment removed for export] *)
Definition P_READER_PUT                 : Z := 0x345c4.   (* [comment removed for export] *)
Definition P_MB_DYN_PREPARE             : Z := 0x34720.   (* [comment removed for export] *)
Definition P_MB_COMMIT                  : Z := 0x34808.   (* [comment removed for export] *)
Definition P_MB_PREPARE                 : Z := 0x348ec.   (* [comment removed for export] *)
Definition P_MB_LIST_ITERATOR_TO        : Z := 0x34d10.   (* [comment removed for export] *)
Definition P_MB_ALLOC                   : Z := 0x34d54.   (* [comment removed for export] *)
Definition P_MB_SUBRANGE_CTOR           : Z := 0x34dfc.   (* [comment removed for export] *)
Definition P_MB_SUBRANGE_DEREF          : Z := 0x35340.   (* [comment removed for export] *)
Definition P_BUFFER_COPY_MB             : Z := 0x353b8.   (* [comment removed for export] *)
Definition P_STDFUNC_CALL_CB_H          : Z := 0x35480.   (* [comment removed for export] *)
Definition P_STDFUNC_CALL_CB_B          : Z := 0x354f8.   (* [comment removed for export] *)
Definition P_STD_THROW_LENGTH_ERROR     : Z := 0x3560c.   (* [comment removed for export] *)
Definition P_SSVC_MAKE_IMPL             : Z := 0x35660.   (* [comment removed for export] *)
Definition P_SP_STATE_ARROW             : Z := 0x35744.   (* [comment removed for export] *)
Definition P_FB_PREPARE                 : Z := 0x35784.   (* [comment removed for export] *)
Definition P_MAKE_SHARED_STATE          : Z := 0x3598c.   (* [comment removed for export] *)
Definition P_SP_IMPL_ARROW              : Z := 0x35b38.   (* [comment removed for export] *)
Definition P_VEC_STATEP_PUSH_BACK       : Z := 0x35b78.   (* [comment removed for export] *)
Definition P_ANYEX_QUERY_CONTEXT        : Z := 0x35c80.   (* [comment removed for export] *)
Definition P_THROW_BAD_EXECUTOR         : Z := 0x35cf8.   (* [comment removed for export] *)
Definition P_CREATE_SSVC                : Z := 0x36124.   (* [comment removed for export] *)
Definition P_ALLOC_OBJ_SSVC             : Z := 0x36154.   (* [comment removed for export] *)
Definition P_DESTROY_ALLOC_SSVC         : Z := 0x3620c.   (* [comment removed for export] *)
Definition P_MAKE_SHARED_IMPL           : Z := 0x36238.   (* [comment removed for export] *)
Definition P_SSVC_DTOR                  : Z := 0x3630c.   (* [comment removed for export] *)
Definition P_SSVC_DELDTOR               : Z := 0x36324.   (* [comment removed for export] *)
Definition P_SSVC_SHUTDOWN              : Z := 0x36360.   (* [comment removed for export] *)
Definition P_NONCOPYABLE_DTOR           : Z := 0x36588.   (* [comment removed for export] *)
Definition P_SHCOUNT_CTOR_IMPL          : Z := 0x3658c.   (* [comment removed for export] *)
Definition P_SHCOUNT_DTOR               : Z := 0x36604.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_DTOR             : Z := 0x3668c.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_DELDTOR          : Z := 0x366a4.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_DISPOSE          : Z := 0x366e0.   (* [comment removed for export] *)
Definition P_SPCB_DESTROY               : Z := 0x366e8.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_GET_DEL          : Z := 0x366f4.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_GET_LDEL         : Z := 0x36718.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_GET_UDEL         : Z := 0x36720.   (* [comment removed for export] *)
Definition P_SPMSD_IMPL_DESTROY         : Z := 0x36728.   (* [comment removed for export] *)
Definition P_VEC_READOP_RESERVE         : Z := 0x36780.   (* [comment removed for export] *)
Definition P_VEC_READOP_THROW_LEN       : Z := 0x36840.   (* [comment removed for export] *)
Definition P_SPLITBUF_READOP_DTOR       : Z := 0x36854.   (* [comment removed for export] *)
Definition P_ALLOC_AT_LEAST_READOP      : Z := 0x368d8.   (* [comment removed for export] *)
Definition P_VEC_READOP_DESTROY         : Z := 0x36910.   (* [comment removed for export] *)
Definition P_DEALLOC_OBJ_SSVC           : Z := 0x369b4.   (* [comment removed for export] *)
Definition P_SHCOUNT_CTOR_STATE         : Z := 0x36a10.   (* [comment removed for export] *)
Definition P_SPCI_STATE_DTOR            : Z := 0x36a88.   (* [comment removed for export] *)
Definition P_SPCI_STATE_DELDTOR         : Z := 0x36ac8.   (* [comment removed for export] *)
Definition P_SPCI_STATE_DISPOSE         : Z := 0x36b0c.   (* [comment removed for export] *)
Definition P_SPCI_STATE_GET_DEL         : Z := 0x36b40.   (* [comment removed for export] *)
Definition P_SPCI_STATE_GET_LDEL        : Z := 0x36b64.   (* [comment removed for export] *)
Definition P_SPCI_STATE_GET_UDEL        : Z := 0x36b6c.   (* [comment removed for export] *)
Definition P_STATE_DTOR                 : Z := 0x36b74.   (* [comment removed for export] *)
Definition P_ANYEX_COPY                 : Z := 0x36c94.   (* [comment removed for export] *)
Definition P_ANYEX_MOVE                 : Z := 0x36cdc.   (* [comment removed for export] *)
Definition P_SPLITBUF_STATEP_DTOR       : Z := 0x37188.   (* [comment removed for export] *)
Definition P_VEC_STATEP_THROW_LEN       : Z := 0x371c4.   (* [comment removed for export] *)
Definition P_ALLOC_AT_LEAST_STATEP      : Z := 0x371d8.   (* [comment removed for export] *)
Definition P_ANYEX_FN_DESTROY           : Z := 0x37a54.   (* [comment removed for export] *)
Definition P_ANYEX_FN_COPY              : Z := 0x37a58.   (* [comment removed for export] *)
Definition P_ANYEX_FN_MOVE              : Z := 0x37a68.   (* [comment removed for export] *)
Definition P_ANYEX_FN_TARGET            : Z := 0x37a78.   (* [comment removed for export] *)
Definition P_ANYEX_FN_QUERY_CTX         : Z := 0x37a7c.   (* [comment removed for export] *)
Definition P_STREAM_CLOSE               : Z := 0x38828.   (* [comment removed for export] *)
Definition P_STATE_REMOVE               : Z := 0x38ab0.   (* [comment removed for export] *)
Definition P_SYNC_READ_OP               : Z := 0x38be0.   (* [comment removed for export] *)
Definition P_HTTP_READ_SOME             : Z := 0x38c9c.   (* [comment removed for export] *)
Definition P_FB_DYN_PREPARE             : Z := 0x39138.   (* [comment removed for export] *)
Definition P_STREAM_READ_SOME           : Z := 0x39204.   (* [comment removed for export] *)
Definition P_BP_PUT_EOF                 : Z := 0x394b8.   (* [comment removed for export] *)
Definition P_BP_PUT                     : Z := 0x395d0.   (* [comment removed for export] *)
Definition P_BP_PARSE_START_LINE        : Z := 0x39a08.   (* [comment removed for export] *)
Definition P_BP_PARSE_FIELDS            : Z := 0x39c3c.   (* [comment removed for export] *)
Definition P_BP_FINISH_HEADER           : Z := 0x39e6c.   (* [comment removed for export] *)
Definition P_BP_CONTENT_LENGTH          : Z := 0x3a044.   (* [comment removed for export] *)
Definition P_BP_PARSE_BODY              : Z := 0x3a0a4.   (* [comment removed for export] *)
Definition P_BP_PARSE_BODY_TO_EOF       : Z := 0x3a188.   (* [comment removed for export] *)
Definition P_BP_PARSE_CHUNK_HEADER      : Z := 0x3a23c.   (* [comment removed for export] *)
Definition P_BP_INNER_PARSE_START_LINE  : Z := 0x3a640.   (* [comment removed for export] *)
Definition P_BP_PARSE_VERSION           : Z := 0x3aa94.   (* [comment removed for export] *)
Definition P_BP_INNER_PARSE_FIELDS      : Z := 0x3ad24.   (* [comment removed for export] *)
Definition P_BP_PARSE_FIELD             : Z := 0x3afec.   (* [comment removed for export] *)
Definition P_BP_DO_FIELD                : Z := 0x3b658.   (* [comment removed for export] *)
Definition P_BP_PARSE_TOKEN_TO_EOL      : Z := 0x3bdf0.   (* [comment removed for export] *)
Definition P_STRING_TO_FIELD            : Z := 0x3bf30.   (* [comment removed for export] *)
Definition P_FIELD_TABLE_EQUALS         : Z := 0x3bffc.   (* [comment removed for export] *)
Definition P_VALIDATE_OPT_TOKEN_LIST    : Z := 0x3c0cc.   (* [comment removed for export] *)
Definition P_BP_DO_FIELD_LAMBDA         : Z := 0x3c15c.   (* [comment removed for export] *)
Definition P_OPT_TOKEN_LIST_INCR        : Z := 0x3c1bc.   (* [comment removed for export] *)
Definition P_BP_PARSE_CHUNK_EXT         : Z := 0x3c290.   (* [comment removed for export] *)
Definition P_EC_ASSIGN_HTTP             : Z := 0x3c54c.   (* [comment removed for export] *)
Definition P_READ_SIZE_FB               : Z := 0x3c630.   (* [comment removed for export] *)
Definition P_CXA_GUARD_ACQUIRE          : Z := 0x3c6a8.   (* [comment removed for export] *)
Definition P_CXA_GUARD_RELEASE          : Z := 0x3c6f8.   (* [comment removed for export] *)
Definition P_STD_TERMINATE              : Z := 0x3c728.   (* [comment removed for export] *)
Definition P_OPDEL                      : Z := 0x58f84.   (* [comment removed for export] *)
Definition P_OPDEL2                     : Z := 0x58f88.   (* [comment removed for export] *)
Definition P_OPDEL_ARR                  : Z := 0x58f8c.   (* [comment removed for export] *)
Definition P_STD_ALIGN                  : Z := 0x5a888.   (* [comment removed for export] *)
Definition P_STD_THROW_SYSTEM_ERROR     : Z := 0x5e884.   (* [comment removed for export] *)
Definition P_CV_DTOR                    : Z := 0x5e9e8.   (* [comment removed for export] *)
Definition P_CV_NOTIFY_ALL              : Z := 0x5ea20.   (* [comment removed for export] *)
Definition P_CV_WAIT                    : Z := 0x5ea3c.   (* [comment removed for export] *)
Definition P_MTX_DTOR                   : Z := 0x5ebb8.   (* [comment removed for export] *)
Definition P_MTX_LOCK                   : Z := 0x5ebd4.   (* [comment removed for export] *)
Definition P_MTX_UNLOCK                 : Z := 0x5ec1c.   (* [comment removed for export] *)
Definition P_ERRNO_LOCATION             : Z := 0x6756c.   (* [comment removed for export] *)
Definition P_ASSERT_FAIL                : Z := 0x67664.   (* [comment removed for export] *)
Definition P_FREE                       : Z := 0x67ed8.   (* [comment removed for export] *)
Definition P_MALLOC                     : Z := 0x68018.   (* [comment removed for export] *)
Definition P_TOWRITE                    : Z := 0x6ab14.   (* [comment removed for export] *)
Definition P_FWRITEX                    : Z := 0x6ad0c.   (* [comment removed for export] *)
Definition P_SNPRINTF                   : Z := 0x6af38.   (* [comment removed for export] *)
Definition P_VFPRINTF                   : Z := 0x6b260.   (* [comment removed for export] *)
Definition P_PRINTF_CORE                : Z := 0x6b410.   (* [comment removed for export] *)
Definition P_POP_ARG                    : Z := 0x6c240.   (* [comment removed for export] *)
Definition P_PAD                        : Z := 0x6c374.   (* [comment removed for export] *)
Definition P_VSNPRINTF                  : Z := 0x6fc98.   (* [comment removed for export] *)
Definition P_SN_WRITE                   : Z := 0x6fd64.   (* [comment removed for export] *)
Definition P_SHLIM                      : Z := 0x7142c.   (* [comment removed for export] *)
Definition P_SHGETC                     : Z := 0x71464.   (* [comment removed for export] *)
Definition P_STRTOLL                    : Z := 0x740bc.   (* [comment removed for export] *)
Definition P_INTSCAN                    : Z := 0x742dc.   (* [comment removed for export] *)
Definition P_BCMP                       : Z := 0x75124.   (* [comment removed for export] *)
Definition P_MEMCHR                     : Z := 0x75128.   (* [comment removed for export] *)
Definition P_MEMCMP                     : Z := 0x751f4.   (* [comment removed for export] *)
Definition P_MEMCPY                     : Z := 0x75224.   (* [comment removed for export] *)
Definition P_MEMMOVE                    : Z := 0x75628.   (* [comment removed for export] *)
Definition P_MEMSET                     : Z := 0x757a4.   (* [comment removed for export] *)
Definition P_STRCMP                     : Z := 0x7589c.   (* [comment removed for export] *)
Definition P_STRLEN                     : Z := 0x7596c.   (* [comment removed for export] *)
Definition P_PTHREAD_COND_BROADCAST     : Z := 0x75fa8.   (* [comment removed for export] *)
Definition P_PTHREAD_COND_DESTROY       : Z := 0x7601c.   (* [comment removed for export] *)
Definition P_PTHREAD_COND_INIT          : Z := 0x761e0.   (* [comment removed for export] *)
Definition P_PRIVATE_COND_SIGNAL        : Z := 0x76984.   (* [comment removed for export] *)
Definition P_PTHREAD_CONDATTR_DESTROY   : Z := 0x76e14.   (* [comment removed for export] *)
Definition P_PTHREAD_CONDATTR_INIT      : Z := 0x76e1c.   (* [comment removed for export] *)
Definition P_PTHREAD_CONDATTR_SETCLOCK  : Z := 0x76e28.   (* [comment removed for export] *)
Definition P_PTHREAD_MUTEX_DESTROY      : Z := 0x77d00.   (* [comment removed for export] *)
Definition P_PTHREAD_MUTEX_INIT         : Z := 0x77d28.   (* [comment removed for export] *)
Definition P_PTHREAD_MUTEX_LOCK         : Z := 0x77da8.   (* [comment removed for export] *)
Definition P_PTHREAD_MUTEX_UNLOCK       : Z := 0x78294.   (* [comment removed for export] *)
Definition P_VM_WAIT                    : Z := 0x78914.   (* [comment removed for export] *)
Definition P_OPNEW                      : Z := 0x78ff8.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition RVT_ALLOCIMPL    : Z := 0x7a740.   (* [comment removed for export] *)
Definition VP_ALLOCIMPL     : Z := 0x7a750.
Definition VS_ALLOCIMPL_0 : Z := 0x2cff8.
Definition VS_ALLOCIMPL_8 : Z := 0x2d030.
Definition VS_ALLOCIMPL_16 : Z := 0x2d108.
Definition VS_ALLOCIMPL_24 : Z := 0x2d17c.
Definition VS_ALLOCIMPL_32 : Z := 0x2d180.
Definition RVT_CONFIG_SVC   : Z := 0x7a3e0.   (* [comment removed for export] *)
Definition VP_CONFIG_SVC    : Z := 0x7a3f0.
Definition VS_CONFIG_SVC_0 : Z := 0x36588.
Definition VS_CONFIG_SVC_8 : Z := 0x2c154.
Definition VS_CONFIG_SVC_16 : Z := 0x2c15c.
Definition VS_CONFIG_SVC_24 : Z := 0x2c160.
Definition VS_CONFIG_SVC_32 : Z := 0x2c164.
Definition RVT_SCHED        : Z := 0x7ab18.   (* [comment removed for export] *)
Definition VP_SCHED         : Z := 0x7ab28.
Definition VS_SCHED_0 : Z := 0x30b70.
Definition VS_SCHED_8 : Z := 0x30c9c.
Definition VS_SCHED_16 : Z := 0x30cc8.
Definition VS_SCHED_24 : Z := 0x2c160.
Definition RVT_SSVC         : Z := 0x7b890.   (* [comment removed for export] *)
Definition VP_SSVC          : Z := 0x7b8a0.
Definition VS_SSVC_0 : Z := 0x3630c.
Definition VS_SSVC_8 : Z := 0x36324.
Definition VS_SSVC_16 : Z := 0x36360.
Definition VS_SSVC_24 : Z := 0x2c160.
Definition RVT_SPCI_IMPL    : Z := 0x7b8f0.   (* [comment removed for export] *)
Definition VP_SPCI_IMPL     : Z := 0x7b900.
Definition VS_SPCI_IMPL_0 : Z := 0x3668c.
Definition VS_SPCI_IMPL_8 : Z := 0x366a4.
Definition VS_SPCI_IMPL_16 : Z := 0x366e0.
Definition VS_SPCI_IMPL_24 : Z := 0x366e8.
Definition VS_SPCI_IMPL_32 : Z := 0x366f4.
Definition VS_SPCI_IMPL_40 : Z := 0x36718.
Definition VS_SPCI_IMPL_48 : Z := 0x36720.
Definition RVT_SPCI_STATE   : Z := 0x7b960.   (* [comment removed for export] *)
Definition VP_SPCI_STATE    : Z := 0x7b970.
Definition VS_SPCI_STATE_0 : Z := 0x36a88.
Definition VS_SPCI_STATE_8 : Z := 0x36ac8.
Definition VS_SPCI_STATE_16 : Z := 0x36b0c.
Definition VS_SPCI_STATE_24 : Z := 0x366e8.
Definition VS_SPCI_STATE_32 : Z := 0x36b40.
Definition VS_SPCI_STATE_40 : Z := 0x36b64.
Definition VS_SPCI_STATE_48 : Z := 0x36b6c.
Definition RVT_PARSER       : Z := 0x7ac00.   (* [comment removed for export] *)
Definition VP_PARSER        : Z := 0x7ac10.
Definition VS_PARSER_0 : Z := 0x2b900.
Definition VS_PARSER_8 : Z := 0x31d5c.
Definition VS_PARSER_16 : Z := 0x31d88.
Definition VS_PARSER_24 : Z := 0x31da4.
Definition VS_PARSER_32 : Z := 0x31da8.
Definition VS_PARSER_40 : Z := 0x31db0.
Definition VS_PARSER_48 : Z := 0x31ed8.
Definition VS_PARSER_56 : Z := 0x31ee8.
Definition VS_PARSER_64 : Z := 0x31f00.
Definition VS_PARSER_72 : Z := 0x31f2c.
Definition VS_PARSER_80 : Z := 0x31f40.
Definition VS_PARSER_88 : Z := 0x31f7c.
Definition RVT_HTTP_ECAT    : Z := 0x7ad30.   (* [comment removed for export] *)
Definition VP_HTTP_ECAT     : Z := 0x7ad40.
Definition VS_HTTP_ECAT_0 : Z := 0x3259c.
Definition VS_HTTP_ECAT_8 : Z := 0x325a8.
Definition VS_HTTP_ECAT_16 : Z := 0x325c0.
Definition VS_HTTP_ECAT_24 : Z := 0x325e8.
Definition VS_HTTP_ECAT_32 : Z := 0x3267c.
Definition VS_HTTP_ECAT_40 : Z := 0x326c4.
Definition VS_HTTP_ECAT_48 : Z := 0x2bc80.
Definition RVT_SYSTEM_ECAT  : Z := 0x7a1f0.   (* [comment removed for export] *)
Definition VP_SYSTEM_ECAT   : Z := 0x7a200.
Definition VS_SYSTEM_ECAT_0 : Z := 0x2bd10.
Definition VS_SYSTEM_ECAT_8 : Z := 0x2b14c.
Definition VS_SYSTEM_ECAT_16 : Z := 0x2bb04.
Definition VS_SYSTEM_ECAT_24 : Z := 0x2bb94.
Definition VS_SYSTEM_ECAT_32 : Z := 0x2bd1c.
Definition VS_SYSTEM_ECAT_40 : Z := 0x2bd60.
Definition VS_SYSTEM_ECAT_48 : Z := 0x2bc80.
Definition RVT_GENERIC_ECAT : Z := 0x7a190.   (* [comment removed for export] *)
Definition VP_GENERIC_ECAT  : Z := 0x7a1a0.
Definition VS_GENERIC_ECAT_0 : Z := 0x2bc88.
Definition VS_GENERIC_ECAT_8 : Z := 0x2b278.
Definition VS_GENERIC_ECAT_16 : Z := 0x2bb04.
Definition VS_GENERIC_ECAT_24 : Z := 0x2bb94.
Definition VS_GENERIC_ECAT_32 : Z := 0x2b108.
Definition VS_GENERIC_ECAT_40 : Z := 0x2bc94.
Definition VS_GENERIC_ECAT_48 : Z := 0x2bc80.
Definition RVT_MISC_ECAT    : Z := 0x7a370.   (* [comment removed for export] *)
Definition VP_MISC_ECAT     : Z := 0x7a380.

(* [comment removed for export] *)
Definition T_ANYEX_TARGET_FNS   : Z := 0x7ba68.   (* [comment removed for export] *)
Definition T_ANYEX_OBJECT_FNS   : Z := 0x7bb20.   (* [comment removed for export] *)
Definition T_ANYEX_PROP_FNS     : Z := 0x7bb40.   (* [comment removed for export] *)
Definition T_ANYEX_PROP_FNS_VOID : Z := 0x7b9c0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_ANYEX_TARGET_FNS_words : list Z := [0x37210; 0x3721c; 0x372c0; 0x0].
Definition T_ANYEX_OBJECT_FNS_words : list Z := [0x37a54; 0x37a58; 0x37a68; 0x37a78].
Definition T_ANYEX_PROP_FNS_words : list Z := [0x37a7c; 0x37a8c; 0x37aa8; 0x37ac4; 0x37b0c; 0x37b44; 0x37b7c; 0x37bc4; 0x37be0; 0x37c18; 0x37c48; 0x37c64; 0x37c80; 0x37cb0; 0x37ccc; 0x37d00; 0x37d48; 0x37d64; 0x37d9c; 0x37de4; 0x37e00].
Definition T_ANYEX_PROP_FNS_VOID_words : list Z := [0x36d44; 0x36d78; 0x36dac; 0x36de0; 0x36e14; 0x36e48; 0x36e7c; 0x36eb0; 0x36ee4; 0x36f18; 0x36f4c; 0x36f80; 0x36fb4; 0x36fe8; 0x3701c; 0x37050; 0x37084; 0x370b8; 0x370ec; 0x37120; 0x37154].

(* [comment removed for export] *)
Definition G_EXF_IN_CALLBACK      : Z := 0x90c74.   (* [comment removed for export] *)
Definition G_EXF_EMPTY            : Z := 0x90c80.   (* [comment removed for export] *)
Definition G_ASIO_SYSTEM_CAT      : Z := 0x90ca0.   (* [comment removed for export] *)
Definition G_ASIO_NETDB_CAT       : Z := 0x90cb0.   (* [comment removed for export] *)
Definition G_ASIO_ADDRINFO_CAT    : Z := 0x90cc0.   (* [comment removed for export] *)
Definition G_ASIO_MISC_CAT        : Z := 0x90cd0.   (* [comment removed for export] *)
Definition G_CALLSTACK_TOP_GUARD  : Z := 0x90ce8.   (* [comment removed for export] *)
Definition G_ID_CONFIG            : Z := 0x90cf0.   (* [comment removed for export] *)
Definition G_ID_SCHED             : Z := 0x90d00.   (* [comment removed for export] *)
Definition G_ID_REACTOR           : Z := 0x90d10.   (* [comment removed for export] *)
Definition G_ID_SSVC              : Z := 0x90d20.   (* [comment removed for export] *)
Definition G_HTTP_CAT             : Z := 0x90d30.   (* [comment removed for export] *)
Definition G_HTTP_CAT_GUARD       : Z := 0x90d68.   (* [comment removed for export] *)
Definition G_FIELD_TABLE          : Z := 0x90d70.   (* [comment removed for export] *)
Definition G_FIELD_TABLE_GUARD    : Z := 0x91ae8.   (* [comment removed for export] *)
Definition G_SYSTEM_CAT_INST      : Z := 0x80870.   (* [comment removed for export] *)
Definition G_GENERIC_CAT_INST     : Z := 0x80988.   (* [comment removed for export] *)
Definition G_INTEROP_CAT_INST     : Z := 0x80950.   (* [comment removed for export] *)
Definition G_MISC_CAT_INST        : Z := 0x80918.   (* [comment removed for export] *)
Definition G_STACK_CHK_GUARD      : Z := 0xb2690.   (* [comment removed for export] *)
Definition G_GOT_STACK_CHK        : Z := 0x7f808.   (* [comment removed for export] *)
Definition G_ERRNO                : Z := 0x925ac.   (* [comment removed for export] *)
Definition G_TP                   : Z := 0x92650.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_SYSTEM_CAT_VPTR : Z := 0x7a200.  Definition W_SYSTEM_CAT_ID : Z := 0xb2ab117a257edfd1.
Definition W_NETDB_CAT_VPTR : Z := 0x7a2c0.  Definition W_NETDB_CAT_ID : Z := 0x0.
Definition W_ADDRINFO_CAT_VPTR : Z := 0x7a320.  Definition W_ADDRINFO_CAT_ID : Z := 0x0.
Definition W_MISC_CAT_VPTR : Z := 0x7a380.  Definition W_MISC_CAT_ID : Z := 0x0.
Definition W_INTEROP_CAT_VPTR : Z := 0x7a260.  Definition W_INTEROP_CAT_ID : Z := 0xb2ab117a257edfd2.
Definition W_GENERIC_CAT_VPTR : Z := 0x7a1a0.  Definition W_GENERIC_CAT_ID : Z := 0xb2ab117a257edfd0.
Definition HTTP_CAT_ID : Z := 0x964627da815bf210.   (* [comment removed for export] *)
Definition CAT_ID_SYSGEN_SHR1 : Z := 0x595588bd12bf6fe8.   (* [comment removed for export] *)
Definition L_CAT_ID_SYSGEN_SHR1 : Z := 0x14de8.  Definition L_HTTP_CAT_ID : Z := 0x14ea8.
Definition TI_NAME_CONFIG : Z := 0x1515b.   (* [comment removed for export] *)
Definition TI_NAME_SCHED  : Z := 0x15449.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition L_STR_SCHEDULER          : Z := 0x10332.   (* [comment removed for export] *)
Definition L_STR_REACTOR            : Z := 0x135f4.   (* [comment removed for export] *)
Definition L_STR_IO_LOCKING         : Z := 0x147aa.   (* [comment removed for export] *)
Definition L_STR_REG_LOCKING        : Z := 0x1033c.   (* [comment removed for export] *)
Definition L_STR_CONCURRENCY_HINT   : Z := 0x13278.   (* [comment removed for export] *)
Definition L_STR_LOCKING            : Z := 0x147a2.   (* [comment removed for export] *)
Definition L_STR_ONE                : Z := 0x12b30.   (* [comment removed for export] *)
Definition L_STR_ZERO               : Z := 0x13834.   (* [comment removed for export] *)
Definition L_STR_MINUS_ONE          : Z := 0x108ae.   (* [comment removed for export] *)
Definition L_STR_FMT_D              : Z := 0x13289.   (* [comment removed for export] *)
Definition L_STR_ASSUME_CONT        : Z := 0x11925.   (* [comment removed for export] *)
Definition L_STR_SPIN               : Z := 0x12d59.   (* [comment removed for export] *)
Definition L_STR_TASK_USEC          : Z := 0x148c0.   (* [comment removed for export] *)
Definition L_STR_WAIT_USEC          : Z := 0x147c5.   (* [comment removed for export] *)
Definition L_EXECUTION_CONTEXT_PROP : Z := 0x15811.   (* [comment removed for export] *)
Definition L_TYPEID_CONFIG          : Z := 0x7a4c0.   (* [comment removed for export] *)
Definition L_TYPEID_SCHED           : Z := 0x7aa48.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FR_PARSER            : Z := 0x0.   (* [comment removed for export] *)
Definition FR_STREAM            : Z := 0x160.   (* [comment removed for export] *)
Definition FR_IOC               : Z := 0x180.   (* [comment removed for export] *)
Definition FR_FB                : Z := 0x198.   (* [comment removed for export] *)
Definition FR_EC                : Z := 0x1c8.   (* [comment removed for export] *)
Definition FR_S2                : Z := 0x1e0.   (* [comment removed for export] *)
Definition FR_S1                : Z := 0x1e8.   (* [comment removed for export] *)
Definition FR_S0                : Z := 0x1f0.   (* [comment removed for export] *)
Definition FR_RA                : Z := 0x1f8.   (* [comment removed for export] *)
Definition FR_SIZE              : Z := 0x200.   (* [comment removed for export] *)
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
Definition zeros (n : nat) : list byte := repeat (b8 0) n.
Definition le8z (z : Z) : list byte := le8 (wz z).
Definition le4z (z : Z) : list byte := le4 (wz z).
Definition u64max : Z := 2^64 - 1.   (* [comment removed for export] *)

(* [comment removed for export] *)
Record ecv := mkEC { ec_val : Z ; ec_cat : Z ; ec_flags : Z }.
Definition EC_clear : ecv := mkEC 0 0 0.
(* [comment removed for export] *)
Definition ec_make (e cat : Z) : ecv := mkEC e cat (if e =? 0 then 2 else 3).
Definition ec_make_loc (e cat loc : Z) : ecv := mkEC e cat (loc + (if e =? 0 then 0 else 1)).
Definition ec_failed (E : ecv) : bool := Z.odd (ec_flags E).
Definition ec_ok (E : ecv) : Prop :=
  0 <= ec_val E < 2^32 /\ 0 <= ec_cat E < 2^64 /\ 0 <= ec_flags E < 2^64 /\ ec_flags E <> 1.

Definition ErrCodeCells (E : ecv) : list cell := [C8 (wz (ec_val E)); C8 (wz (ec_cat E)); C8 (wz (ec_flags E))].
Definition ErrCode (m : mem) (a : Z) (E : ecv) : Prop := rw_cells rsegs m a (ErrCodeCells E) /\ ec_ok E.

(* [comment removed for export] *)
Definition EC_http (e : Z) : ecv := ec_make e G_HTTP_CAT.                 (* [comment removed for export] *)
Definition EC_http_loc (e loc : Z) : ecv := ec_make_loc e G_HTTP_CAT loc. (* [comment removed for export] *)
Definition EC_asio_eof : ecv := ec_make ASIO_ERR_EOF G_MISC_CAT_INST.    (* [comment removed for export] *)

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
Definition FlatBuf (LB : list block) (m : mem) (a : Z) (F : fbv) (ds : list byte) : Prop :=
  rw_cells rsegs m a (FlatBufCells F) /\ fb_ok LB F /\ zlength ds = fb_size F
  /\ (F <> FB_empty -> exists pre junk,
        rw_cells rsegs m (fb_begin F) [CB (Z.to_nat (fb_in F - fb_begin F)) pre; CB (length ds) ds;
                                     CB (Z.to_nat (fb_end F - fb_out F)) junk]).

(* [comment removed for export] *)
Definition PMutexCells (lk : Z) : list cell := [CB 4 (zeros 4); C4 (wz lk); CB 32 (zeros 32)].
Definition PMutex (m : mem) (a : Z) (lk : Z) : Prop := rw_cells rsegs m a (PMutexCells lk) /\ (lk = 0 \/ lk = EBUSY) /\ a mod 4 = 0.
(* [comment removed for export] *)
Definition PMutexZeroCells : list cell := [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
Definition PCondCells (clk : Z) : list cell := [CB 16 (zeros 16); C4 (wz clk); CB 12 (zeros 12); C4 (wz 0); CB 4 (zeros 4); C8 (wz 0)].
Definition PCond (m : mem) (a : Z) (clk : Z) : Prop := rw_cells rsegs m a (PCondCells clk) /\ (clk = 0 \/ clk = CLOCK_MONOTONIC) /\ a mod 8 = 0.

(* [comment removed for export] *)
Record svch := mkSVC { sv_vptr : Z ; sv_ti : Z ; sv_id : Z ; sv_owner : Z ; sv_next : Z ; sv_destroy : Z }.
Definition SvcHdrCells (S : svch) : list cell :=
  [C8 (wz (sv_vptr S)); C8 (wz (sv_ti S)); C8 (wz (sv_id S)); C8 (wz (sv_owner S)); C8 (wz (sv_next S)); C8 (wz (sv_destroy S))].

(* [comment removed for export] *)
Definition CookieCells (junk7 : list byte) : list cell := [CB 8 (zeros 8); CB 7 junk7].

(* [comment removed for export] *)
Definition AllocImpl (LB : list block) (m : mem) (a : Z) : Prop :=
  exists p junk, In (p, a, SZ_ALLOCIMPL) LB /\ rw_cells rsegs m a [C8 (wz VP_ALLOCIMPL); CB 8 junk].

(* [comment removed for export] *)
Definition Registry (LB : list block) (m : mem) (r : Z) (owner first lk : Z) : Prop :=
  exists p j0 j7, In (p, r, NEWSZ_REG) LB
  /\ rw_cells rsegs m r [CB 8 j0]
  /\ PMutex m (r + O_REG_MUTEX) lk
  /\ rw_cells rsegs m (r + O_REG_OWNER) [C8 (wz owner); C8 (wz first)]
  /\ rw_cells rsegs m (r + SZ_REG) (CookieCells j7).

(* [comment removed for export] *)
Definition ConfigSvc (LB : list block) (m : mem) (c : Z) (S : svch) : Prop :=
  exists p j4 j7, In (p, c, NEWSZ_CFG) LB
  /\ rw_cells rsegs m c (SvcHdrCells S ++ [C4 (wz (2^32 - 1)); CB 4 j4] ++ CookieCells j7)
  /\ sv_vptr S = VP_CONFIG_SVC /\ sv_destroy S = P_DESTROY_ALLOC_CONFIG.

(* [comment removed for export] *)
Record schv := mkSCH { sch_hdr : svch ; sch_lk : Z ; sch_stopped : Z ; sch_shutdown : Z }.
Definition Scheduler (LB : list block) (m : mem) (s : Z) (S : schv) : Prop :=
  exists p j50 jm j109 je jt j219 j7, In (p, s, NEWSZ_SCH) LB
  /\ rw_cells rsegs m s (SvcHdrCells (sch_hdr S))
  /\ rw_cells rsegs m (s + O_SCH_ONE_THREAD) [CB 2 [b8 0; b8 0]; CB 6 j50]           (* [comment removed for export] *)
  /\ rw_cells rsegs m (s + O_SCH_MUTEX) [CB 8 jm]                                     (* [comment removed for export] *)
  /\ PMutex m (s + O_SCH_PMUTEX) (sch_lk S)                                            (* [comment removed for export] *)
  /\ rw_cells rsegs m (s + O_SCH_SPIN) [C4 (wz 0); CB 1 [b8 1]; CB 3 j109]            (* [comment removed for export] *)
  /\ rw_cells rsegs m (s + O_SCH_EVENT) [CB 8 je]                                     (* [comment removed for export] *)
  /\ PCond m (s + O_SCH_COND) CLOCK_MONOTONIC                                          (* [comment removed for export] *)
  /\ rw_cells rsegs m (s + O_SCH_EVSTATE)
       [C8 (wz 0);                                   (* [comment removed for export] *)
        C8 (wz 0); C8 (wz P_SCHED_GET_DEFAULT_TASK); (* [comment removed for export] *)
        C8 (wz 0); C8 (wz 0); C4 (wz 0); CB 4 jt;    (* [comment removed for export] *)
        CB 3 [b8 1; b8 (sch_stopped S); b8 (sch_shutdown S)]; CB 5 j219;   (* [comment removed for export] *)
        C8 (wz 0);                                   (* [comment removed for export] *)
        C8 (wz 0); C8 (wz 0);                        (* [comment removed for export] *)
        C8 (wz u64max); C8 (wz u64max);              (* [comment removed for export] *)
        C8 (wz 0)]                                   (* [comment removed for export] *)
  /\ rw_cells rsegs m (s + SZ_SCH) (CookieCells j7)
  /\ sv_vptr (sch_hdr S) = VP_SCHED /\ sv_destroy (sch_hdr S) = P_DESTROY_ALLOC_SCHED
  /\ (sch_stopped S = 0 \/ sch_stopped S = 1) /\ (sch_shutdown S = 0 \/ sch_shutdown S = 1).

(* [comment removed for export] *)
Record spcv := mkSPC { spc_vptr : Z ; spc_use : Z ; spc_weak : Z ; spc_init : Z }.
Definition SpcHdrCells (C : spcv) (j7 : list byte) : list cell :=
  [C8 (wz (spc_vptr C)); C4 (wz (spc_use C)); C4 (wz (spc_weak C)); C8 (wz 0); CB 1 [b8 (spc_init C)]; CB 7 j7].
Definition spc_ok (C : spcv) : Prop := 0 <= spc_use C < 2^31 /\ 0 <= spc_weak C < 2^31 /\ (spc_init C = 0 \/ spc_init C = 1).

(* [comment removed for export] *)
Record implv := mkIMPL { im_hdr : spcv ; im_lk : Z ; im_vb : Z ; im_states : list Z ; im_vcap : Z }.
Definition ImplBlock (LB : list block) (m : mem) (b : Z) (I : implv) : Prop :=
  exists p j7, In (p, b, SZ_SPCI_IMPL) LB /\ rblock_range b SZ_SPCI_IMPL
  /\ rw_cells rsegs m b (SpcHdrCells (im_hdr I) j7) /\ spc_ok (im_hdr I) /\ spc_vptr (im_hdr I) = VP_SPCI_IMPL
  /\ PMutex m (b + O_SPC_STORAGE + O_IMPL_MUTEX) (im_lk I)
  /\ rw_cells rsegs m (b + O_SPC_STORAGE + O_IMPL_VEC_BEGIN)
       [C8 (wz (im_vb I)); C8 (wz (im_vb I + 8 * zlength (im_states I))); C8 (wz (im_vb I + 8 * im_vcap I))]
  /\ zlength (im_states I) <= im_vcap I
  /\ ((im_vcap I = 0 /\ im_vb I = 0)
      \/ (exists q junk, In (q, im_vb I, 8 * im_vcap I) LB /\ rblock_range (im_vb I) (8 * im_vcap I) /\ 0 < im_vcap I
           /\ rw_cells rsegs m (im_vb I) [CB (8 * length (im_states I)) (flat_map le8z (im_states I));
                                         CB (Z.to_nat (8 * (im_vcap I - zlength (im_states I)))) junk])).

(* [comment removed for export] *)
Definition AnyExecCells (a ioc : Z) (j16 : list byte) : list cell :=
  [C8 (wz ioc); CB 16 j16; C8 (wz T_ANYEX_OBJECT_FNS); C8 (wz a); C8 (wz T_ANYEX_TARGET_FNS); C8 (wz T_ANYEX_PROP_FNS)].

(* [comment removed for export] *)
Record statev := mkST { st_hdr : spcv ; st_lk : Z ; st_fb : fbv ; st_code : Z ; st_nread : Z ; st_nread_bytes : Z }.
Definition StateBlock (LB : list block) (m : mem) (b ioc implb : Z) (S : statev) (ds : list byte) : Prop :=
  exists p j7 j16 j4, In (p, b, SZ_SPCI_STATE) LB /\ rblock_range b SZ_SPCI_STATE
  /\ rw_cells rsegs m b (SpcHdrCells (st_hdr S) j7) /\ spc_ok (st_hdr S) /\ spc_vptr (st_hdr S) = VP_SPCI_STATE
  /\ rw_cells rsegs m (b + 32 + O_ST_EXEC) (AnyExecCells (b + 32 + O_ST_EXEC) ioc j16)
  /\ rw_cells rsegs m (b + 32 + O_ST_WP_PX) [C8 (wz (implb + O_SPC_STORAGE)); C8 (wz implb)]
  /\ PMutex m (b + 32 + O_ST_MUTEX) (st_lk S)
  /\ FlatBuf LB m (b + 32 + O_ST_FB) (st_fb S) ds
  /\ PCond m (b + 32 + O_ST_CV) 0
  /\ rw_cells rsegs m (b + 32 + O_ST_OP)
       [C8 (wz 0);                          (* [comment removed for export] *)
        C4 (wz (st_code S)); CB 4 j4;       (* [comment removed for export] *)
        C8 (wz 0);                          (* [comment removed for export] *)
        C8 (wz (st_nread S)); C8 (wz (st_nread_bytes S));
        C8 (wz 0); C8 (wz 0);               (* [comment removed for export] *)
        C8 (wz u64max); C8 (wz u64max)]     (* [comment removed for export] *)
  /\ (st_code S = STREAM_OK \/ st_code S = STREAM_EOF) /\ 0 <= st_nread S < 2^63 /\ 0 <= st_nread_bytes S < 2^63.

(* [comment removed for export] *)
Definition StreamSvc (LB : list block) (m : mem) (v : Z) (S : svch) (implb : Z) : Prop :=
  exists p j7, In (p, v, NEWSZ_SSVC) LB
  /\ rw_cells rsegs m v (SvcHdrCells S ++ [C8 (wz (implb + O_SPC_STORAGE)); C8 (wz implb)] ++ CookieCells j7)
  /\ sv_vptr S = VP_SSVC /\ sv_destroy S = P_DESTROY_ALLOC_SSVC.

(* [comment removed for export] *)
Definition BasicStreamCells (stateb : Z) : list cell :=
  [C8 (wz (stateb + O_SPC_STORAGE)); C8 (wz stateb); C8 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
Definition IoCtxCells (allocb regb schedb : Z) : list cell := [C8 (wz allocb); C8 (wz regb); C8 (wz schedb)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IoWorld2 (LB : list block) (m : mem) (ioc allocb regb cfgb schedb : Z) : Prop :=
  rw_cells rsegs m ioc (IoCtxCells allocb regb schedb)
  /\ AllocImpl LB m allocb
  /\ Registry LB m regb ioc schedb 0
  /\ ConfigSvc LB m cfgb (mkSVC VP_CONFIG_SVC L_TYPEID_CONFIG 0 ioc 0 P_DESTROY_ALLOC_CONFIG)
  /\ Scheduler LB m schedb (mkSCH (mkSVC VP_SCHED L_TYPEID_SCHED 0 ioc cfgb P_DESTROY_ALLOC_SCHED) 0 0 0).
(* [comment removed for export] *)
Definition ImplBlockV (LB : list block) (m : mem) (implb : Z) (use weak : Z) (states : list Z) (vcap : Z) : Prop :=
  exists vb, ImplBlock LB m implb (mkIMPL (mkSPC VP_SPCI_IMPL use weak 1) 0 vb states vcap).
(* [comment removed for export] *)
Definition IoWorld3 (LB : list block) (m : mem) (ioc bs allocb regb cfgb schedb ssvcb implb stateb : Z)
           (F : fbv) (ds : list byte) (code nread nread_bytes : Z) : Prop :=
  rw_cells rsegs m ioc (IoCtxCells allocb regb schedb)
  /\ rw_cells rsegs m bs (BasicStreamCells stateb)
  /\ AllocImpl LB m allocb
  /\ Registry LB m regb ioc ssvcb 0
  /\ ConfigSvc LB m cfgb (mkSVC VP_CONFIG_SVC L_TYPEID_CONFIG 0 ioc 0 P_DESTROY_ALLOC_CONFIG)
  /\ Scheduler LB m schedb (mkSCH (mkSVC VP_SCHED L_TYPEID_SCHED 0 ioc cfgb P_DESTROY_ALLOC_SCHED) 0 0 0)
  /\ StreamSvc LB m ssvcb (mkSVC VP_SSVC 0 G_ID_SSVC ioc schedb P_DESTROY_ALLOC_SSVC) implb
  /\ ImplBlockV LB m implb 1 2 [stateb + O_SPC_STORAGE] 1
  /\ StateBlock LB m stateb ioc implb (mkST (mkSPC VP_SPCI_STATE 1 1 1) 0 F code nread nread_bytes) ds.
(* [comment removed for export] *)
Definition IoWorld4 (LB : list block) (m : mem) (ioc allocb regb cfgb schedb ssvcb implb : Z) : Prop :=
  rw_cells rsegs m ioc (IoCtxCells allocb regb schedb)
  /\ AllocImpl LB m allocb
  /\ Registry LB m regb ioc ssvcb 0
  /\ ConfigSvc LB m cfgb (mkSVC VP_CONFIG_SVC L_TYPEID_CONFIG 0 ioc 0 P_DESTROY_ALLOC_CONFIG)
  /\ Scheduler LB m schedb (mkSCH (mkSVC VP_SCHED L_TYPEID_SCHED 0 ioc cfgb P_DESTROY_ALLOC_SCHED) 0 0 0)
  /\ StreamSvc LB m ssvcb (mkSVC VP_SSVC 0 G_ID_SSVC ioc schedb P_DESTROY_ALLOC_SSVC) implb
  /\ ImplBlockV LB m implb 1 1 [] 1.

(* [comment removed for export] *)
Lemma ErrCode_clear_intro : forall m a, rw_cells rsegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> ErrCode m a EC_clear.
Proof. intros m a H. split; [exact H|]. unfold ec_ok, EC_clear; cbn; lia. Qed.
Lemma FlatBuf_empty_intro : forall LB m a,
  rw_cells rsegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz u64max)] -> FlatBuf LB m a FB_empty [].
Proof.
  intros LB m a H. split; [exact H|]. split; [left; reflexivity|]. split; [reflexivity|]. intros NE. exfalso. apply NE. reflexivity.
Qed.

End HCW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XS.
  Context {HCEIL : HeapCeil}.

Definition wcells (zs : list Z) : list cell := map (fun z => C8 (wz z)) zs.

Definition XStatics (m : mem) : Prop :=
     rw_cells rsegs m VP_ALLOCIMPL   (wcells [VS_ALLOCIMPL_0; VS_ALLOCIMPL_8; VS_ALLOCIMPL_16; VS_ALLOCIMPL_24; VS_ALLOCIMPL_32])
  /\ rw_cells rsegs m VP_CONFIG_SVC  (wcells [VS_CONFIG_SVC_0; VS_CONFIG_SVC_8; VS_CONFIG_SVC_16; VS_CONFIG_SVC_24; VS_CONFIG_SVC_32])
  /\ rw_cells rsegs m VP_SCHED       (wcells [VS_SCHED_0; VS_SCHED_8; VS_SCHED_16; VS_SCHED_24])
  /\ rw_cells rsegs m VP_SSVC        (wcells [VS_SSVC_0; VS_SSVC_8; VS_SSVC_16; VS_SSVC_24])
  /\ rw_cells rsegs m VP_SPCI_IMPL   (wcells [VS_SPCI_IMPL_0; VS_SPCI_IMPL_8; VS_SPCI_IMPL_16; VS_SPCI_IMPL_24; VS_SPCI_IMPL_32; VS_SPCI_IMPL_40; VS_SPCI_IMPL_48])
  /\ rw_cells rsegs m VP_SPCI_STATE  (wcells [VS_SPCI_STATE_0; VS_SPCI_STATE_8; VS_SPCI_STATE_16; VS_SPCI_STATE_24; VS_SPCI_STATE_32; VS_SPCI_STATE_40; VS_SPCI_STATE_48])
  /\ rw_cells rsegs m VP_PARSER      (wcells [VS_PARSER_0; VS_PARSER_8; VS_PARSER_16; VS_PARSER_24; VS_PARSER_32; VS_PARSER_40; VS_PARSER_48; VS_PARSER_56; VS_PARSER_64; VS_PARSER_72; VS_PARSER_80; VS_PARSER_88])
  /\ rw_cells rsegs m VP_HTTP_ECAT   (wcells [VS_HTTP_ECAT_0; VS_HTTP_ECAT_8; VS_HTTP_ECAT_16; VS_HTTP_ECAT_24; VS_HTTP_ECAT_32; VS_HTTP_ECAT_40; VS_HTTP_ECAT_48])
  /\ rw_cells rsegs m T_ANYEX_OBJECT_FNS (wcells T_ANYEX_OBJECT_FNS_words)
  /\ rw_cells rsegs m T_ANYEX_TARGET_FNS (wcells T_ANYEX_TARGET_FNS_words)
  /\ rw_cells rsegs m T_ANYEX_PROP_FNS   (wcells T_ANYEX_PROP_FNS_words)
  /\ rw_cells rsegs m T_ANYEX_PROP_FNS_VOID (wcells T_ANYEX_PROP_FNS_VOID_words)
  /\ rw_cells rsegs m (L_TYPEID_CONFIG + 8) (wcells [TI_NAME_CONFIG])
  /\ rw_cells rsegs m (L_TYPEID_SCHED + 8)  (wcells [TI_NAME_SCHED])
  /\ rw_cells rsegs m G_SYSTEM_CAT_INST (wcells [W_SYSTEM_CAT_VPTR; W_SYSTEM_CAT_ID])
  /\ rw_cells rsegs m G_MISC_CAT_INST   (wcells [W_MISC_CAT_VPTR; W_MISC_CAT_ID]).

(* [comment removed for export] *)
Definition XStatics_ivs : list (Z * Z) :=
  [(VP_ALLOCIMPL, VP_ALLOCIMPL + 40); (VP_CONFIG_SVC, VP_CONFIG_SVC + 40); (VP_SCHED, VP_SCHED + 32); (VP_SSVC, VP_SSVC + 32);
   (VP_SPCI_IMPL, VP_SPCI_IMPL + 56); (VP_SPCI_STATE, VP_SPCI_STATE + 56); (VP_PARSER, VP_PARSER + 96); (VP_HTTP_ECAT, VP_HTTP_ECAT + 56);
   (T_ANYEX_OBJECT_FNS, T_ANYEX_OBJECT_FNS + 32); (T_ANYEX_TARGET_FNS, T_ANYEX_TARGET_FNS + 32);
   (T_ANYEX_PROP_FNS, T_ANYEX_PROP_FNS + 168); (T_ANYEX_PROP_FNS_VOID, T_ANYEX_PROP_FNS_VOID + 168);
   (L_TYPEID_CONFIG + 8, L_TYPEID_CONFIG + 16); (L_TYPEID_SCHED + 8, L_TYPEID_SCHED + 16);
   (G_SYSTEM_CAT_INST, G_SYSTEM_CAT_INST + 16); (G_MISC_CAT_INST, G_MISC_CAT_INST + 16)].
Scheme kc__1 := Elimination for Corelib.Init.Datatypes.prod Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.

(* [comment removed for export] *)
Lemma XStatics_transport : forall W m m',
  XStatics m -> munch W m m' -> wmono rsegs m m' ->
  Forall (fun iv : Z * Z => (0x7bd60 <= fst iv \/ snd iv <= 0x7a190) /\ (0x80928 <= fst iv \/ snd iv <= 0x80870)) W ->
  XStatics m'.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.XS.XStatics); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.I); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.Lists.List.Forall_inv); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.Lists.List.Forall_inv_tail); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VP_ALLOCIMPL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.XS.wcells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_ALLOCIMPL_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_ALLOCIMPL_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_ALLOCIMPL_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_ALLOCIMPL_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_ALLOCIMPL_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VP_CONFIG_SVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_CONFIG_SVC_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_CONFIG_SVC_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_CONFIG_SVC_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_CONFIG_SVC_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_CONFIG_SVC_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VP_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SCHED_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SCHED_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SCHED_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SCHED_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VP_SSVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SSVC_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SSVC_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SSVC_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SSVC_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VP_SPCI_IMPL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_IMPL_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_IMPL_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_IMPL_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_IMPL_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_IMPL_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_IMPL_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_IMPL_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VP_SPCI_STATE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_STATE_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_STATE_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_STATE_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_STATE_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_STATE_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_STATE_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_SPCI_STATE_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VP_PARSER); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_56); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_72); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_80); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_PARSER_88); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VP_HTTP_ECAT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_HTTP_ECAT_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_HTTP_ECAT_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_HTTP_ECAT_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_HTTP_ECAT_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_HTTP_ECAT_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_HTTP_ECAT_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.VS_HTTP_ECAT_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.T_ANYEX_OBJECT_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.T_ANYEX_OBJECT_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.T_ANYEX_TARGET_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.T_ANYEX_TARGET_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.T_ANYEX_PROP_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.T_ANYEX_PROP_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.T_ANYEX_PROP_FNS_VOID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.T_ANYEX_PROP_FNS_VOID_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.L_TYPEID_CONFIG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.TI_NAME_CONFIG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.L_TYPEID_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.TI_NAME_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.G_SYSTEM_CAT_INST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.W_SYSTEM_CAT_VPTR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.W_SYSTEM_CAT_ID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.G_MISC_CAT_INST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.W_MISC_CAT_VPTR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.W_MISC_CAT_ID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.or_morph); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@kc__1 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))|] [|@iv; @FW; @W; @l; @p; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__arith; @H1; @IH; @hi; @lo; @z; @a; @HA; @n; @A; @x; @y; @m; @H14; @H13; @H12; @H11; @H10; @H9; @H8; @H7; @H6; @H5; @H4; @H3; @H2; @H0; @H; @D; @WM; @MU; @XS; @m'|] "#D6#g%R#u#x$<$=$;$C$E#{##%@%C%:%8%6%4%,${#$$s$$#a#d#g$k$f$a$[$T#-#)#,#.#b#%#*#1#5#9#=#A#E#I#M#Q#U#Y#]#f#e#0%G#&#4#2#8#6#<#:#@$.#>#D#B#H#k#(#F#L%S#'#J#P#N#T#R#X$4#V#\#p#Z#j#n#m#r#+$3$6$5$9$K$L#/#^#_#`#q#s#t#w#~$#$($,$7$8$:$F$H$N$M$O$P$I$Q$)$%$Z$Y$X$W$V$`$_$^$]$\$e$d$c$b$j$i$h$g$r$q$p$o$n$m$l$z$y$x$w$v$u$t%+%*%)%(%'%&%%%$%#$~$}$|%3%2%1%0%/%.%-%5%7%9%;%<%=%>%?%B%A%E%D#3#7#;#?#C#G#K#O#S#W#[#c%N%P%Q#l#y$S$2#o$A$@#z$*#}$J$>%L%M%K#|$B$?$G$-$U%H%O%J%I%F$R$&%R$1$0#v$/$D$'$+J%/%%0'#*%%1$%2$%3'%4*%5%#6%%6&%7$%8%%9*%:&%;/%<)%=$%>%#U$%?*%@&%A'%B$%C$%D5%E)%F'$%&%G-%H(%I&%J/%K%%L&%M&%N%%O%%P$%Q'USdSS'Sb'#'#'#'#'#USe#USf#USe(USf#USs#k##&#USgS$WStSFS4S$WSuCSFS4VSvDD-Sb-#-#'#-#-#-#-#-#-#'#'#'#'#'#'#'#'#3#WSwDDK-Sb-#-#'#-#-#-#-#'#-#'#-#-#'#'#'#'#'#3#'1'#'#'#-#-#'#'#-#'#'#'#'#3#'Sb'#'#'#'#'#'#-#'#'#-#'#'#-#'#-#'#'#'#3#'-'#-#-#-#'#'#'#'#3#-s#--#-#'#-#'#-#'#'#'#'#3#-s#8-#-#-#-#-#'#'#'#'#3#-s#E'#-#-#'#'#-#'#-#'#'#'#3#'s#_'#'#-#'#-#'#'#'#'#'#3#--'#'#'#'#'#'#'#'#3#-+-#-#'#'#'#'#3#-s#-'#'#'#'#'#-#'#'#'#'#3#--'#-#'#'#'#'#'#'#3#-s#6-#'#'#-#'#'#'#'#'#3#'-'#-#-#'#-#'#'#'#3#-5'#'#'#'#'#'#3#-s#G-#'#'#'#'#'#'#3#'s$$'#-#-#'#'#'#'#'#'#3#'s#r'#-#'#'#-#'#'#'#3#'s$K-#-#'#'#'#3#%s$ms%$WSxDDK's%5'#'#-#-#'#'#-#-#'#'#'#'#3#%1s$o*3#'s%T-#'#-#'#-#-#'#'#-#'#'#'#3#%s$ks%D'-'#'#-#'#'#'#'#3#%s#+s$k*-##=#j#$s%e#Es%f#ST%s%2S$+S$K%#s%B#%#%s$tS$%&s%##$#*&#Es%o,KAS$SXSFk#%$#j#&s&&#HSSEs%t1#j#%#SyAS$S0STk#%*#,SSS4S$Es%y6#,SSSFS4A#S5S0k#%%#k##(#k#'s&2#j#(s&##AS$S1Shk#%4#IDDSFS4,SS#S$Es&(A#IDDSXSFYSzs&*s###S4KUs#$$+S2S/%#ST%SXS2*$#ASFS2S/&Si&#&#&#&#CD#CD&CDSiDD$#DD&#F#S_CD*CD-CD/DD$#DD&#F#S_DD.%F#S_DD*-F#S_HSN,SN.#,SN/#,SN&#,SN)#,SN,#,SN-#,SN4#,SN5#USdSNVSjDSXUS{DXSkD$S4#VSjDSFXSkD$S$#US|DUS}D4Ds&0GDs&W(D$H#)&GEEF#IGDs&i4Ds&'(D$H#)*GEEF#I6+GEEF'#4Ds%s(D#H+).GEEF#I4Ds%l(D+H#)1GEEF#I62GEEF&#/3GEEF*#US~EGDSb(D0H#)7GEEF#IGDs&{7D&#(D#H9);GEEF#I/<GEEF'#(D0H*)>GEEF#I(D(H5)@GEEF#I/AGEEF%#6BGEEF(#(D,HA)s#$GEEF#I(D@H2)s#&GEEF#I6s#'GEEF%#\Sls#(GEEF(6#\Sls#)GEEF87#VT#s#*F.SmSnVT$KS4WT%Sm#Snm$%#WT&DT'S$XT(KS4$#l#)*)#l#*s#4s#3#l#+s#;s#:#j#,D#j#-D#j#.D#j#/D#%s&eS4%SFs&X*$#%s&FS4%SFs&=*$##&#+S$S4%#s&m#s$0#%%s&M#s$.#*%#+S4SF%#SX%STS4*$#k##'#k##.#k#,D#k#-D#k#.D#k#/D#ZKSTS0S2SoS$S/l#0;$#IDDSTSXYT)s'Js$C#SFS$US4#8s#{s#z&#,SS&SFA#S2S/m#%#l#1s$(s$'#j#%s$+#j#2s$/#j#&s'c#j#3D#j#4D#V#S$Kj#5D#j#5D#YT*DDs$8#Kj#6SS#ZT+SSs$Gs$D#S1SFj#7s$L#j#8D#j#9D#AS1S4S$k##s$P#k#8D#k#9D#HD,DT,#,DT-#,DT.#,DT/#,DT0#9#$CS0S.#,DT1*,DT2#,DT3#,DT4#,DT5#9#$CS0S-#,DT61,DT7#,DT8#,DT9#9#$CS0S,#,DT:7,DT;#,DT<#,DT=#9#$CS0S+#,DT>=,DT?#,DT@#,DTA#,DTB#,DTC#,DTD#9#$CS0S*#,DTEs#&,DTF#,DTG#,DTH#,DTI#,DTJ#,DTK#9#$CS0S%#,DTLs#/,DTM#,DTN#,DTO#,DTP#,DTQ#,DTR#,DTS#,DTT#,DTU#,DTV#,DTW#9#$CS0S##,DTXs#=,DTY#,DTZ#,DT[#,DT\#,DT]#,DT^#9#$CS0R#9T_$CS0Q#9T`$CS0P#9Ta$CS0O#9Tb$CS0N#3s(`+Tc#,DTds#P9#$CS0%#+Te',DTfs#T9#$CS0%#,DTgs#W,DTh#9#$CS0L#,DTis#[,DTj#9#$CS0M##'##,##1##7##:##=##@##s####s#-##s#<##s#F##s#P##s#W##s#^##s#f#j####$CS5S-s#b$CS5S,s#]$CS5S+s#X$CS5S*s#P$CS5S%s#H$CS5S#s#;$CS5Rs#3$CS5Qs#2$CS5Ps#1$CS5Os#0$CS5Ns#/$CS5s#-s#+$CS5s#*s#($CS5Ls#%$CS5MB#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CShS.s$*$CS1S-s$$$CS1S,s#{$CS1S+s#v$CS1S*s#n$CS1S%s#f$CS1S#s#Y$CS1Rs#Q$CS1Qs#P$CS1Ps#O$CS1Os#N$CS1Ns#M$CS1s#Ks#I$CS1s#Hs#F$CS1Ls#C$CS1Ms#@#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CS/S-s$A$CS/S,s$<$CS/S+s$7$CS/S*s$/$CS/S%s$'$CS/S#s#v$CS/Rs#n$CS/Qs#m$CS/Ps#l$CS/Os#k$CS/Ns#j$CS/s#hs#f$CS/s#es#c$CS/Ls#`$CS/Ms#]#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CS/S.s$e##$j##%#$CS2S,s$[$CS2S+s$V$CS2S*s$N$CS2S%s$F$CS2S#s$9$CS2Rs$1$CS2Qs$0$CS2Ps$/$CS2Os$.$CS2Ns$-$CS2s$+s$)$CS2s$(s$&$CS2Ls$#$CS2Ms#|#$##&##(##*##,##.##0##2##4##6##8##:##<#$CSoS-s$|$CSDS,s$w$CSDS+s$r$CSDS*s$j$CSDS%s$b$CSDS#s$U$CSDRs$M$CSDQs$L$CSDPs$K$CSDOs$J$CSDNs$I$CSDs$Gs$E$CSDs$Ds$B$CSDLs$?$CSDMs$<#$##&##(##*##,##.##0##2##4##6##8##:##<#$CS6S,s%6$CS6S+s%1$CS6S*s%)$CS6S%s$}$CS6S#s$p$CS6Rs$h$CS6Qs$g$CS6Ps$f$CS6Os$e$CS6Ns$d$CS6s$bs$`$CS6s$_s$]$CS6Ls$Z$CS6Ms$W#$##&##(##*##,##.##0##2##4##6##8##:##<#$CS6S.s%^$CS6S-s%X##%#%#j##'#$CSHS+s%P$CSHS*s%H$CSHS%s%@$CSHS#s%3$CSHRs%+$CSHQs%*$CSHPs%)$CSHOs%($CSHNs%'$CSHs%%s%#$CSHs$~s$|$CSHLs$y$CSHMs$v#$##&##(##*##,##.##0##2##4##6##8##:#$CTkS,s%o$CSGS+s%j$CSGS*s%b$CSGS%s%Z$CSGS#s%M$CSGRs%E$CSGQs%D$CSGPs%C$CSGOs%B$CSGNs%A$CSGs%?s%=$CSGs%<s%:$CSGLs%7$CSGMs%4#$##&##(##*##,##.##0##2##4##6##8##:#$CS7S+s&'$CS7S*s%{$CS7S%s%s$CS7S#s%f$CS7Rs%^$CS7Qs%]$CS7Ps%\$CS7Os%[$CS7Ns%Z$CS7s%Xs%V$CS7s%Us%S$CS7Ls%P$CS7Ms%M#$##&##(##*##,##.##0##2##4##6##8##:#$CS7S.s&S$CS7S-s&M$CS7S,s&H##&#%##'#j##)#$CSJS*s&>$CSJS%s&6$CSJS#s&)$CSJRs%}$CSJQs%|$CSJPs%{$CSJOs%z$CSJNs%y$CSJs%ws%u$CSJs%ts%r$CSJLs%o$CSJMs%l#$##&##(##*##,##.##0##2##4##6##8#$CTlS+s&^$CSIS*s&V$CSIS%s&N$CSIS#s&A$CSIRs&9$CSIQs&8$CSIPs&7$CSIOs&6$CSINs&5$CSIs&3s&1$CSIs&0s&.$CSILs&+$CSIMs&(#$##&##(##*##,##.##0##2##4##6##8#$CS8S*s&m$CS8S%s&e$CS8S#s&X$CS8Rs&P$CS8Qs&O$CS8Ps&N$CS8Os&M$CS8Ns&L$CS8s&Js&H$CS8s&Gs&E$CS8Ls&B$CS8Ms&?#$##&##(##*##,##.##0##2##4##6##8#$CS8S.s'D$CS8S-s'>$CS8S,s'9$CS8S+s'4##'#%##'##)#j##+#$CSLS%s'($CSLS#s&w$CSLRs&o$CSLQs&n$CSLPs&m$CSLOs&l$CSLNs&k$CSLs&is&g$CSLs&fs&d$CSLLs&a$CSLMs&^#$##&##(##*##,##.##0##2##4##6#$CTmS*s'F$CSKS%s'>$CSKS#s'1$CSKRs')$CSKQs'($CSKPs''$CSKOs'&$CSKNs'%$CSKs'#s&}$CSKs&|s&z$CSKLs&w$CSKMs&t#$##&##(##*##,##.##0##2##4##6#$CS9S%s'S$CS9S#s'F$CS9Rs'>$CS9Qs'=$CS9Ps'<$CS9Os';$CS9Ns':$CS9s'8s'6$CS9s'5s'3$CS9Ls'0$CS9Ms'-#$##&##(##*##,##.##0##2##4##6#$CS9S.s(1$CS9S-s(+$CS9S,s(&$CS9S+s'}$CS9S*s'u##(#%##'##)##+#j##-#$CSOS#s'e$CSORs']$CSOQs'\$CSOPs'[$CSOOs'Z$CSONs'Y$CSOs'Ws'U$CSOs'Ts'R$CSOLs'O$CSOMs'L#$##&##(##*##,##.##0##2##4#$CTnS%s(*$CSMS#s'y$CSMRs'q$CSMQs'p$CSMPs'o$CSMOs'n$CSMNs'm$CSMs'ks'i$CSMs'hs'f$CSMLs'c$CSMMs'`#$##&##(##*##,##.##0##2##4#$CS:S#s(0$CS:Rs(($CS:Qs('$CS:Ps(&$CS:Os(%$CS:Ns($$CS:s'~s'|$CS:s'{s'y$CS:Ls'v$CS:Ms's#$##&##(##*##,##.##0##2##4#$CS:S.s(v$CS:S-s(p$CS:S,s(k$CS:S+s(f$CS:S*s(^$CS:S%s(V##)#%##'##)##+##-#j##/#$CSQRs(G$CSQQs(F$CSQPs(E$CSQOs(D$CSQNs(C$CSQs(As(?$CSQs(>s(<$CSQLs(9$CSQMs(6#$##&##(##*##,##.##0##2#$CToS#s(a$CSPRs(Y$CSPQs(X$CSPPs(W$CSPOs(V$CSPNs(U$CSPs(Ss(Q$CSPs(Ps(N$CSPLs(K$CSPMs(H#$##&##(##*##,##.##0##2#$CS;Rs(j$CS;Qs(i$CS;Ps(h$CS;Os(g$CS;Ns(f$CS;s(ds(b$CS;s(as(_$CS;Ls(\$CS;Ms(Y#$##&##(##*##,##.##0##2#$CS;S.s)[$CS;S-s)U$CS;S,s)P$CS;S+s)K$CS;S*s)C$CS;S%s);$CS;S#s).##*#%##'##)##+##-##/#j##1#$CSUQs),$CSUPs)+$CSUOs)*$CSUNs))$CSUs)'s)%$CSUs)$s(~$CSULs({$CSUMs(x#$##&##(##*##,##.##0#$CTpRs)=$CSRQs)<$CSRPs);$CSROs):$CSRNs)9$CSRs)7s)5$CSRs)4s)2$CSRLs)/$CSRMs),#$##&##(##*##,##.##0#$CS<Qs)K$CS<Ps)J$CS<Os)I$CS<Ns)H$CS<s)Fs)D$CS<s)Cs)A$CS<Ls)>$CS<Ms);#$##&##(##*##,##.##0#$CS<S.s*<$CS<S-s*6$CS<S,s*1$CS<S+s*,$CS<S*s*$$CS<S%s)x$CS<S#s)k$CS<Rs)c##+#%##'##)##+##-##/##1#j##3#$CSYPs)i$CSYOs)h$CSYNs)g$CSYs)es)c$CSYs)bs)`$CSYLs)]$CSYMs)Z#$##&##(##*##,##.#$CTqQs)x$CSVPs)w$CSVOs)v$CSVNs)u$CSVs)ss)q$CSVs)ps)n$CSVLs)k$CSVMs)h#$##&##(##*##,##.#$CS=Ps*($CS=Os*'$CS=Ns*&$CS=s*$s)~$CS=s)}s){$CS=Ls)x$CS=Ms)u#$##&##(##*##,##.#$CS=S.s*u$CS=S-s*o$CS=S,s*j$CS=S+s*e$CS=S*s*]$CS=S%s*U$CS=S#s*H$CS=Rs*@$CS=Qs*?##,#%##'##)##+##-##/##1##3#j##5#$CS[Os*F$CS[Ns*E$CS[s*Cs*A$CS[s*@s*>$CS[Ls*;$CS[Ms*8#$##&##(##*##,#$CTrPs*S$CSZOs*R$CSZNs*Q$CSZs*Os*M$CSZs*Ls*J$CSZLs*G$CSZMs*D#$##&##(##*##,#$CS>Os*]$CS>Ns*\$CS>s*Zs*X$CS>s*Ws*U$CS>Ls*R$CS>Ms*O#$##&##(##*##,#$CS>S.s+N$CS>S-s+H$CS>S,s+C$CS>S+s+>$CS>S*s+6$CS>S%s+.$CS>S#s*}$CS>Rs*u$CS>Qs*t$CS>Ps*s##-#%##'##)##+##-##/##1##3##5#j##7#$CS]Ns*{$CS]s*ys*w$CS]s*vs*t$CS]Ls*q$CS]Ms*n#$##&##(##*#$CTsOs+*$CS\Ns+)$CS\s+'s+%$CS\s+$s*~$CS\Ls*{$CS\Ms*x#$##&##(##*#$CS?Ns+2$CS?s+0s+.$CS?s+-s++$CS?Ls+($CS?Ms+%#$##&##(##*#$CS?S.s,#$CS?S-s+y$CS?S,s+t$CS?S+s+o$CS?S*s+g$CS?S%s+_$CS?S#s+R$CS?Rs+J$CS?Qs+I$CS?Ps+H$CS?Os+G##.#%##'##)##+##-##/##1##3##5##7#j##9#$CS`s+Os+M$CS`s+Ls+J$CS`Ls+G$CS`Ms+D#$##&##(#$CTtNs+Y$CS^s+Ws+U$CS^s+Ts+R$CS^Ls+O$CS^Ms+L#$##&##(#$CS@s+^s+\$CS@s+[s+Y$CS@Ls+V$CS@Ms+S#$##&##(#$CS@S.s,P$CS@S-s,J$CS@S,s,E$CS@S+s,@$CS@S*s,8$CS@S%s,0$CS@S#s,#$CS@Rs+w$CS@Qs+v$CS@Ps+u$CS@Os+t$CS@Ns+s##/#%##'##)##+##-##/##1##3##5##7##9#j##;#$CScs+zs+x$CScLs+u$CScMs+r#$##&#$CTus,'s,%$CSas,$s+~$CSaLs+{$CSaMs+x#$##&#$CSAs,)s,'$CSALs,$$CSAMs+}#$##&#$CSAS.s,y$CSAS-s,s$CSAS,s,n$CSAS+s,i$CSAS*s,a$CSAS%s,Y$CSAS#s,L$CSARs,D$CSAQs,C$CSAPs,B$CSAOs,A$CSANs,@$CSAs,>s,<##0#%##'##)##+##-##/##1##3##5##7##9##;#j##=#$CSpLs,C$CSpMs,@#$#$CSqs,Ls,J$CSrLs,G$CSrMs,D#$#$CS'Ls,J$CS'Ms,G#$#$CS'S.s-B$CS'S-s-<$CS'S,s-7$CS'S+s-2$CS'S*s-*$CS'S%s,~$CS'S#s,q$CS'Rs,i$CS'Qs,h$CS'Ps,g$CS'Os,f$CS'Ns,e$CS's,cs,a$CS's,`s,^##1#%##'##)##+##-##/##1##3##5##7##9##;##=#j##?#$CS3Ms,f$CTvLs,k$CS(Ms,h$CS(S.s-b$CS(S-s-\$CS(S,s-W$CS(S+s-R$CS(S*s-J$CS(S%s-B$CS(S#s-5$CS(Rs--$CS(Qs-,$CS(Ps-+$CS(Os-*$CS(Ns-)$CS(s-'s-%$CS(s-$s,~$CS(Ls,{##2#%##'##)##+##-##/##1##3##5##7##9##;##=#:s.#5#-s0T'#'#'#-#-#-#-#'#'#'#'#3#%s2ds2:&s/g&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#5#+s2_#%#s3<#s#)#%s2ns2b%&s2y#$#*&#-s3x'#'#'#3#+s2k#%#s3H#s#5#%%s3(#/#*%#.S)s#90s#:s#:#j#:DK%S$KUTw#j#;D#j#:D#XTxDDTys0q.D#j#<D#j#8D#.Ds2|5K.D#j#:SW#.D8BSWDDDSESE00$s#&9#;DDDDDDS&111S&)s3&s3&(s#&:#.Ds3_1DDJ3J/s#';$s3`s3`#2s#Ms#'s#M;5#.S)s#&0s#'s#'#.Ds3B1DDJ8J4s#,@)s3Cs3C#2s#*s#)s#*>%#<s#,s#)@>(#4Ds30(Ds06H#)s0=GEEF#I4Ds#'7D&#(D#Hs0?)s0AGEEF#I/s0BGEEF'#(Ds06H*)s0DGEEF#I(D(Hs0;)s0FGEEF#I/s0GGEEF%#6s0HGEEF(#l#)#s/}s/wl#*s0Os0K#l#+s0[s0R#l#0#s#/K=s#;s#05#m##s#<%s3nS.+S.s#E%#s3~#%#%s3TS.%&s3_#$#*&#m#+#+S.s$#%#s4*#-#%%s3f#+#*%#m#)#>S.s$*#?CSBSCS(S.s/MSaS3S'#:s/G5#-s1~'#-#-#'#'#-#'#'#'#'#3#%s42s3Y+s3Zs#e%#s4B#%#%s3ts3]%&s4##$#*&#+s3as#`%#s4I#,#%%s4)#*#*%#.S)0011#.Ds3i;DDDDDDS&s#`s#`s#`S&s#Xs3js3j#s#us#is#R1DDJs#aJs#]3,#s4Rs4Rs#Q2535,&#.S)2033#1DDJs#eJs#a70's44s44s#P2545.$#<740.'#4Ds3r(Ds1'H#)s1.GEEF#I7D%s#O(D#Hs1/)s11GEEF#I/s12GEEF&#(Ds1&H))s14GEEF#I(D(Hs1+)s16GEEF#I/s17GEEF%#6s18GEEF(#l#)#s0ms0gl#*s1?s1;#l#+s1Ks1B#l#0#>K=s#%?4#m##s#&%s4^S-+S-s$5%#s4n#%#%s4DS-%&s4O#$#*&#m#+#+S-s#D%#s4v#-#%%s4V#+#*%#m#)#>S-s#K#?CSBSCS(S-s06S^S3S'#:s015#-s$y'#'#-#-#'#'#-#'#'#'#3#%s4~s4<5s$^+s4>#%#s53#&#%s4es4A%&s4p#$#*&#3s5k+s4F#%#s5;#.#%%s4w#+#*%#.S)2033#.Ds4N.D,BSWDDDSESEs$Ss$Ss$Gs$q-#;DDDDDDS&s$Ts$Ts$TS&s$Ls4Qs4Q%6.#1DDJs$UJs$Q6.#s5Fs5Fs$E2969.(#.S)5066#1DDJs$YJs$U:2's5(s5(s$D28780$#<:720'#4Ds4Y(Ds1wH#)s1~GEEF#I4D97D&#(D#Hs2$)s2&GEEF#I/s2'GEEF'#(Ds1wH*)s2)GEEF#I(D(Hs1|)s2+GEEF#I/s2,GEEF%#6s2-GEEF(#l#)#s1bs1\l#*s24s20#l#+s2@s27#l#0#AK=s#)B5#m##s#*%s5SS,+S,s#3%#s5c#%#%s59S,%&s5D#$#*&#m#+#+S,s#I%#s5k#-#%%s5K#+#*%#m#)#>S,s#P#?CSBSCS(S,s1%S\S3S'#:s0|5#'s69-#'#'#-#'#'#'#'#'#'#3#%s5ss5%+s5&s#S%#s6'#%#%s5Ys5)%&s5d#$#*&#+s5-s#R%#s6.#,#%%s5j#*#*%#.S)0011#.Ds55;DDDDDDS&s%Es%Es%ES&s%=s56s56#s#cs#[s#P1DDJs%FJs%B3,#s67s67s%62535,&#.S)2033#1DDJs%JJs%F70's5us5us%52545.$#<740.'#4Ds5>(Ds2hH#)s2oGEEF#I7D%s#O(D#Hs2p)s2rGEEF#I/s2sGEEF&#(Ds2gH))s2uGEEF#I(D(Hs2l)s2wGEEF#I/s2xGEEF%#6s2yGEEF(#l#)#s2Rs2Ll#*s3$s2|#l#+s30s3'#l#0#>K=s#%?4#m##s#&%s6CS++S+s$#%#s6S#%#%s6)S+%&s64#$#*&#m#+#+S+s#D%#s6[#-#%%s6;#+#*%#m#)#>S+s#K#?CSBSCS(S+s1kSZS3S'#:s1c5#-s#L'#-#'#'#'#'#'#3#%s6`s5d&s&8&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#5#+s5v#%#s7%#6#%s6Ws5y%&s6b#$#*&#'s7P'#'#3#+s6%#%#s70#A#%%s6l#.#*%#.S)s#%0s#&s#&#.Ds6-.D,BSWDDDSESEs&Hs&Hs&<9-#;DDDDDDS&s&Is&Is&IS&s&As60s60%9.#1DDJs&JJs&F9.#s7;s7;s&:2s#,9s#,.(#.S)8099#1DDJs&NJs&J=2's6ys6ys&92;:;0$#<=:20'#4Ds68(Ds3lH#)s3sGEEF#I4D97D&#(D#Hs3u)s3wGEEF#I/s3xGEEF'#(Ds3lH*)s3zGEEF#I(D(Hs3q)s3|GEEF#I/s3}GEEF%#6s3~GEEF(#l#)#s3Ws3Ql#*s4)s4%#l#+s45s4,#l#0#AK=s#,B5#m##s#-%s7HS*+S*s#6%#s7X#%#%s7.S*%&s79#$#*&#m#+#+S*s#Y%#s7`#-#%%s7@#+#*%#m#)#>S*s#`#?CSBSCS(S*s2gSVS3S'#:s2_5#-s$R'#'#'#-#'#'#'#'#3#%s7fs6b+s6cs#T%#s7v#%#%s7Ls6f%&s7W#$#*&#+s6js#P%#s7}#,#%%s7]#*#*%#.S)0011#.Ds6r;DDDDDDS&s'8s'8s'8S&s'0s6ss6s#s#ds#Ys#N1DDJs'9Js'53,#s8*s8*s')2535,&#.S)2033#1DDJs'=Js'970's7hs7hs'(2545.$#<740.'#4Ds6{(Ds4[H#)s4bGEEF#I7D%s#M(D#Hs4c)s4eGEEF#I/s4fGEEF&#(Ds4ZH))s4hGEEF#I(D(Hs4_)s4jGEEF#I/s4kGEEF%#6s4lGEEF(#l#)#s4Es4?l#*s4ss4o#l#+s5#s4v#l#0#>K=s#%?4#m##s#&%s86S%+S%s$$%#s8F#%#%s7xS%%&s8'#$#*&#m#+#+S%s#B%#s8N#-#%%s8.#+#*%#m#)#>S%s#I#?CSBSCS(S%s3LSRS3S'#:s3?5#-s&5-#'#-#-#'#'#'#'#3#%s8Ts7D&s$C&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#5#+s7n#%#s91#s#.#%s8cs7q%&s8n#$#*&#'s9]'#'#'#'#3#+s7{#%#s9>#s#;#%%s8z#0#*%#.S)s#?0s#@s#@#.Ds8'.D,BSWDDDSESEs(Vs(Vs(J;-#;DDDDDDS&s(Ws(Ws(WS&s(Os8*s8*%;.#1DDJs(XJs(T;.#s9Is9Is(H2s#F;s#F.(#.S):0;;#1DDJs(\Js(X?2's9+s9+s(G2=<=0$#<?<20'#4Ds82(Ds5zH#)s6%GEEF#I4D97D&#(D#Hs6')s6)GEEF#I/s6*GEEF'#(Ds5zH*)s6,GEEF#I(D(Hs6#)s6.GEEF#I/s6/GEEF%#6s60GEEF(#l#)#s5es5_l#*s67s63#l#+s6Cs6:#l#0#AK=s#.B5#m##s#/%s9VS#+S#s#8%#s9f#%#%s9<S#%&s9G#$#*&#m#+#+S#s#t%#s9n#-#%%s9N#+#*%#m#)#>S#s#{#?CSBSCS(S#s4^SPS3S'#:s4V5#-s'V'#-#-#-#'#'#'#'#'#3#%s9us8[+s8\s%c%#s:)#%#%s9[s8_%&s9f#$#*&#+s8cs%_%#s:0#,#%%s9l#*#*%#.S)0011#.Ds8k;DDDDDDS&s)Gs)Gs)GS&s)?s8ls8l#s%ss%hs%]1DDJs)HJs)D3,#s:9s:9s)82535,&#.S)2033#1DDJs)LJs)H70's9ws9ws)72545.$#<740.'#4Ds8t(Ds6jH#)s6qGEEF#I7D%s%\(D#Hs6r)s6tGEEF#I/s6uGEEF&#(Ds6iH))s6wGEEF#I(D(Hs6n)s6yGEEF#I/s6zGEEF%#6s6{GEEF(#l#)#s6Ts6Nl#*s7&s6~#l#+s72s7)#l#0#>K=s#%?4#m##s#&%s:ER+Rs&3%#s:U#%#%s:+R%&s:6#$#*&#m#+#+Rs#C%#s:]#-#%%s:=#+#*%#m#)#>Rs#J#?CSBSCS(Rs5DSMS3S'#:s5C5#'s;*'#-#-#'#'#'#'#'#'#3#%s:ds9?+s9@s(D%#s:t#%#%s:Js9C%&s:U#$#*&#+s9Gs(C%#s:{#,#%%s:[#*#*%#.S)0011#.Ds9O;DDDDDDS&s*6s*6s*6S&s*.s9Ps9P#s(Ts(Ls(A1DDJs*7Js*33,#s;(s;(s*'2535,&#.S)2033#1DDJs*;Js*770's:fs:fs*&2545.$#<740.'#4Ds9X(Ds7YH#)s7`GEEF#I7D%s(@(D#Hs7a)s7cGEEF#I/s7dGEEF&#(Ds7XH))s7fGEEF#I(D(Hs7])s7hGEEF#I/s7iGEEF%#6s7jGEEF(#l#)#s7Cs7=l#*s7qs7m#l#+s7}s7t#l#0#>K=s#%?4#m##s#&%s;4Q+Qs(p%#s;D#%#%s:vQ%&s;%#$#*&#m#+#+Qs#C%#s;L#-#%%s;,#+#*%#m#)#>Qs#J#?CSBSCS(Qs61SKS3S'#:s605#'s#L'#'#'#-#'#'#'#3#%s;Qs9~+s:#s)1%#s;a#%#%s;7s:&%&s;B#$#*&#+s:*s)0%#s;h#,#%%s;H#*#*%#.S)0011#.Ds:2;DDDDDDS&s+#s+#s+#S&s*ws:3s:3#s)As)9s).1DDJs+$Js*|3,#s;qs;qs*p2535,&#.S)2033#1DDJs+(Js+$70's;Ss;Ss*o2545.$#<740.'#4Ds:;(Ds8FH#)s8MGEEF#I7D%s)-(D#Hs8N)s8PGEEF#I/s8QGEEF&#(Ds8EH))s8SGEEF#I(D(Hs8J)s8UGEEF#I/s8VGEEF%#6s8WGEEF(#l#)#s80s8*l#*s8^s8Z#l#+s8js8a#l#0#>K=s#%?4#m##s#&%s;}P+Ps)]%#s<1#%#%s;cP%&s;n#$#*&#m#+#+Ps#A%#s<9#-#%%s;u#+#*%#m#)#>Ps#H#?CSBSCS(Ps6xSIS3S'#:s6w5#-s$7'#'#'#'#'#3#%s<<s:a&s%{&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#5#+s;O#%#s=9#s#N#%s<ks;R%&s<v#$#*&#-s,Z'#'#'#3#+s;[#%#s=E#s#Z#%%s=%#/#*%#.S)s#^0s#_s#_#.Ds;c.D,BSWDDDSESEs,]s,]s,Q:-#;DDDDDDS&s,^s,^s,^S&s,Vs;fs;f%:.#1DDJs,_Js,[:.#s=Ps=Ps,O2s#e:s#e.(#.S)90::#1DDJs,cJs,_>2's=2s=2s,N2<;<0$#<>;20'#4Ds;n(Ds:%H#)s:,GEEF#I4D97D&#(D#Hs:.)s:0GEEF#I/s:1GEEF'#(Ds:%H*)s:3GEEF#I(D(Hs:*)s:5GEEF#I/s:6GEEF%#6s:7GEEF(#l#)#s9ls9fl#*s:>s::#l#+s:Js:A#l#0#AK=s#-B5#m##s#.%s=]O+Os#7%#s=m#%#%s=CO%&s=N#$#*&#m#+#+Os$4%#s=u#-#%%s=U#+#*%#m#)#>Os$;#?CSBSCS(Os8VSGS3S'#:s8U5#-s(r-#'#'#'#'#'#3#%s=ys<9+s<:s#S%#s>-#%#%s=_s<=%&s=j#$#*&#+s<As#N%#s>4#,#%%s=p#*#*%#.S)0011#.Ds<I;DDDDDDS&s-Ks-Ks-KS&s-Cs<Js<J#s#cs#Ws#L1DDJs-LJs-H3,#s>=s>=s-<2535,&#.S)2033#1DDJs-PJs-L70's={s={s-;2545.$#<740.'#4Ds<R(Ds:nH#)s:uGEEF#I7D%s#K(D#Hs:v)s:xGEEF#I/s:yGEEF&#(Ds:mH))s:{GEEF#I(D(Hs:r)s:}GEEF#I/s:~GEEF%#6s;#GEEF(#l#)#s:Xs:Rl#*s;*s;&#l#+s;6s;-#l#0#>K=s#%?4#m##s#&%s>IN+Ns$#%#s>Y#%#%s>/N%&s>:#$#*&#m#+#+Ns#@%#s>a#-#%%s>A#+#*%#m#)#>Ns#G#?CSBSCS(Ns9@SDS3S'#:s9<5#-s-9'#'#-#-#'#'#'#'#'#3#+s<ys9L%s>i#5s.a+%#%#s>z#&#%s>P(%&s>[#$#*&#+,s9V%#s?%#-#%%s>a#*#*%#.S)1022#.D4.Ds9_BSWDDDSESEs.=s.=s.1s.ss9`#;DDDDDDS&s.>s.>s.>S&s.677%5s9a#1DDJs.?Js.;5.#s?0s?0s./2858.(#.S)4055#1DDJs.CJs.?92's>ns>ns..27670$#<9620'#4Ds=:4Ds9j7D$#(Ds;cH#)s;jGEEF#I7D%&(D#Hs;k)s;mGEEF#I/s;nGEEF&#(Ds;bH))s;pGEEF#I(D(Hs;g)s;rGEEF#I/s;sGEEF%#6s;tGEEF(#l#)#s;Ms;Gl#*s;{s;w#l#+s<+s;~#l#0#BK=s#)s##6#m##s#*%s?>s9}+s9~s#3%#s?N#%#%s?$s:%%&s?/#$#*&#m#+#+s:*s#I%#s?V#-#%%s?6#+#*%#m#)#>s:1s#P#?CSBSCS(s:2s:0S1S3S'#:s:-5#-s/X-#-#-#-#'#-#'#'#'#3#+s=ds:A%s?^#+$s#S%#s?n#%#%s?D'%&s?O#$#*&#++s:J%#s?u#,#%%s?U#*#*%#.S)0011#.D3;DDDDDDS&s/0s/0s/0S&s/(44#s#cs:Ss#Q1DDJs/1Js/-3,#s?~s?~s.}2535,&#.S)2033#1DDJs/5Js/170's?`s?`s.|2545.$#<740.'#4Ds=~7D#s#P(Ds<TH#)s<[GEEF#I7D%s#S(D#Hs<\)s<^GEEF#I/s<_GEEF&#(Ds<SH))s<aGEEF#I(D(Hs<X)s<cGEEF#I/s<dGEEF%#6s<eGEEF(#l#)#s<>s<8l#*s<ls<h#l#+s<xs<o#l#0#?K=s#&@5#m##s#'%s@/s:j+s:ks$$%#s@?#%#%s?qs:n%&s?|#$#*&#m#+#+s:ss#E%#s@G#-#%%s@'#+#*%#m#)#>s:zs#L#?CSBSCS(s:{s:ySTS3S'#:s:v5#%s@Cs@%5s03+s@'#%#s@T#&#%s@*s@*%&s@5#$#*&#3sA1+s@/#%#s@\#.#%%s@<#+#*%#.S)2033#.Ds@7.D,BSWDDDSESEs/ts/ts/hs0F-#;DDDDDDS&s/us/us/uS&s/ms@:s@:%6.#1DDJs/vJs/r6.#s@gs@gs/f2969.(#.S)5066#1DDJs/zJs/v:2's@Is@Is/e28780$#<:720'#(Ds=;Hs=4)s=BGEEF#I4D87Ds=7#(D#Hs=D)s=FGEEF#I/s=GGEEF'#(Ds=;Hs=;)s=IGEEF#I(D(Hs=@)s=KGEEF#I/s=LGEEF%#6s=MGEEF(#l#)#s=&s<|l#*s=Ts=P#l#+s=`s=W#l#0#@K=s#(A4#m##s#)%s@sL+Ls#2%#sA'#%#%s@YL%&s@d#$#*&#m#+#+Ls#<%#sA/#-#%%s@k#+#*%#m#)#>Ls#C#?CSBSCS(Ls;]S$S3S'#:s;Z5#'s>o-#-#-#'#'#'#3#%sA3s?3+s?4s#N%#sAC#%#%s@us?7%&sA$#$#*&#+s?;s#M%#sAJ#,#%%sA*#*#*%#.S)0011#.Ds?C;DDDDDDS&s0as0as0aS&s0Ys?Ds?D#s#^s#Vs#K1DDJs0bJs0^3,#sASsASs0R2535,&#.S)2033#1DDJs0fJs0b70'sA5sA5s0Q2545.$#<740.'#4Ds?L(Ds>(H#)s>/GEEF#I7D%s#K(D#Hs>0)s>2GEEF#I/s>3GEEF&#(Ds>'H))s>5GEEF#I(D(Hs>,)s>7GEEF#I/s>8GEEF%#6s>9GEEF(#l#)#s=ns=hl#*s>@s><#l#+s>Ls>C#l#0#>K=s#%?4#m##s#&%sA_M+Ms#z%#sAo#%#%sAEM%&sAP#$#*&#m#+#+Ms#@%#sAw#-#%%sAW#+#*%#m#)#>Ms#G#?CSBSCS(Ms<EKS3S'#8s2-s2<s#K#8s2/s2-s$4#8s21s2-s%&#8s23s2-s%x#8s25s2-s&e#8s27s2-s(F#8s29s2-s)4#8s2;s2-s*$#8s2=s2-s*p#8s2?s2-s,5#8s2As2-s-$#8s2Cs2-s.*#8s2Es2-s.w#8s2Gs2-s/m#8s2Is2-s0^#j#=s2K#j#>s2M#V#S$Kj##s2P#j##s2q#@s2rs2qs2S#Kj#>s2t#j#?s2x#V#S$Kj##s2{#j##s3B#@s3Cs3@s3$#Kj#?s3E#j#@s3K#V#S$Kj##s3N#j##s3s#@s3ts3os3U#Kj#@s3v#j#As3~#V#S$Kj##s4%#j##s4L#@s4Ms4Fs4.#Kj#As4O#j#Bs4Y#V#S$Kj##s4\#j##s5)#@s5*s4}s4g#Kj#Bs5,#j#Cs58#V#S$Kj##s5;#j##s5f#@s5gs5\s5H#Kj#Cs5i#j#Ds5w#V#S$Kj##s5z#j##s6K#@s6Ls6?s6-#Kj#Ds6N#j#Es6^#V#S$Kj##s6a#j##s74#@s75s7&s6r#Kj#Es77#j#Fs7I#V#S$Kj##s7L#j##s7}#@s7~s7ms7_#Kj#Fs8$#j#Gs88#V#S$Kj##s8;#j##s8n#@s8os8\s8P#Kj#Gs8q#j#Hs9+#V#S$Kj##s9.#j##s9c#@s9ds9Os9E#Kj#Hs9f#j#Is9~#V#S$Kj##s:%#j##s:\#@s:]s:Fs:>#Kj#Is:_#j#1s:y#V#S$Kj##s:|#j##s;Y#@s;Zs;As;;#Kj#1s;\#j#Js;x#V#S$Kj##s;{#j##s<Z#@s<[s<@s<<#Kj#Js<]#j#Ks<{#V#S$Kj##s<~#j##s>I#@s>Js=Cs=A#SXUSgSTm#$#l#Ls>Ys>U#j#%s@R#j#MsC\#j#NsC^#j#OsC`#j#PsCb#j#<Tz#j#&sCp##"). Qed.

(* [comment removed for export] *)
Definition XStatics_img_ok : bool :=
  forallb (fun ac : Z * list Z =>
             match image_bytes rsegs (fst ac) (8 * length (snd ac))%nat with
             | Some bs => if list_eq_dec (fun a b : byte => @base.decide (a = b) (bv_eq_dec 8 a b)) bs (flat_map le8z (snd ac)) then true else false
             | None => false end)
    [(VP_ALLOCIMPL, [VS_ALLOCIMPL_0; VS_ALLOCIMPL_8; VS_ALLOCIMPL_16; VS_ALLOCIMPL_24; VS_ALLOCIMPL_32]);
     (VP_CONFIG_SVC, [VS_CONFIG_SVC_0; VS_CONFIG_SVC_8; VS_CONFIG_SVC_16; VS_CONFIG_SVC_24; VS_CONFIG_SVC_32]);
     (VP_SCHED, [VS_SCHED_0; VS_SCHED_8; VS_SCHED_16; VS_SCHED_24]);
     (VP_SSVC, [VS_SSVC_0; VS_SSVC_8; VS_SSVC_16; VS_SSVC_24]);
     (VP_SPCI_IMPL, [VS_SPCI_IMPL_0; VS_SPCI_IMPL_8; VS_SPCI_IMPL_16; VS_SPCI_IMPL_24; VS_SPCI_IMPL_32; VS_SPCI_IMPL_40; VS_SPCI_IMPL_48]);
     (VP_SPCI_STATE, [VS_SPCI_STATE_0; VS_SPCI_STATE_8; VS_SPCI_STATE_16; VS_SPCI_STATE_24; VS_SPCI_STATE_32; VS_SPCI_STATE_40; VS_SPCI_STATE_48]);
     (VP_PARSER, [VS_PARSER_0; VS_PARSER_8; VS_PARSER_16; VS_PARSER_24; VS_PARSER_32; VS_PARSER_40; VS_PARSER_48; VS_PARSER_56; VS_PARSER_64; VS_PARSER_72; VS_PARSER_80; VS_PARSER_88]);
     (VP_HTTP_ECAT, [VS_HTTP_ECAT_0; VS_HTTP_ECAT_8; VS_HTTP_ECAT_16; VS_HTTP_ECAT_24; VS_HTTP_ECAT_32; VS_HTTP_ECAT_40; VS_HTTP_ECAT_48]);
     (T_ANYEX_OBJECT_FNS, T_ANYEX_OBJECT_FNS_words); (T_ANYEX_TARGET_FNS, T_ANYEX_TARGET_FNS_words);
     (T_ANYEX_PROP_FNS, T_ANYEX_PROP_FNS_words); (T_ANYEX_PROP_FNS_VOID, T_ANYEX_PROP_FNS_VOID_words);
     (L_TYPEID_CONFIG + 8, [TI_NAME_CONFIG]); (L_TYPEID_SCHED + 8, [TI_NAME_SCHED]);
     (G_SYSTEM_CAT_INST, [W_SYSTEM_CAT_VPTR; W_SYSTEM_CAT_ID]); (G_MISC_CAT_INST, [W_MISC_CAT_VPTR; W_MISC_CAT_ID])].
Lemma XStatics_img_ok_true : XStatics_img_ok = true.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.XS.XStatics_img_ok)|] Array.empty "##&###(#'#(#&#)#*#VECDWFCGDm$$##"). Qed.

(* [comment removed for export] *)
Definition HttpCatCells (built : bool) : list cell :=
  if built then [C8 (wz VP_HTTP_ECAT); C8 (wz HTTP_CAT_ID); CB 40 (zeros 40)] else [CB 56 (zeros 56)].
Definition HttpCatGuardCells (built : bool) : list cell :=
  if built then [CB 8 (b8 1 :: b8 1 :: zeros 6)] else [CB 8 (zeros 8)].
Definition HttpCat (m : mem) (built : bool) : Prop :=
  rw_cells rsegs m G_HTTP_CAT (HttpCatCells built) /\ rw_cells rsegs m G_HTTP_CAT_GUARD (HttpCatGuardCells built).

(* [comment removed for export] *)
Definition CanaryReads (m : mem) : Prop :=
  Lib.PropExec.rdn rsegs m (Z_to_bv 64 G_GOT_STACK_CHK) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 G_STACK_CHK_GUARD))
  /\ exists can : Z, Lib.PropExec.rdn rsegs m (Z_to_bv 64 G_STACK_CHK_GUARD) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).

End XS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RBL.
  Context {HCEIL : HeapCeil}.

Record rbnode := mkRBN { rbn_parent : Z ; rbn_left : Z ; rbn_right : Z ; rbn_color : Z }.
Definition RBnodeCells (n : rbnode) (pad : list byte) : list cell :=
  [C8 (wz (rbn_parent n)); C8 (wz (rbn_left n)); C8 (wz (rbn_right n)); C4 (wz (rbn_color n)); CB 4 pad].
Definition RBcells (m : mem) (ns : gmap Z rbnode) : Prop :=
  map_Forall (fun (a : Z) (n : rbnode) => exists pad, rw_cells rsegs m a (RBnodeCells n pad)) ns.

Record dlnode := mkDLN { dl_next : Z ; dl_prev : Z }.
Definition DLnodeCells (n : dlnode) : list cell := [C8 (wz (dl_next n)); C8 (wz (dl_prev n))].
Definition DLcells (m : mem) (ls : gmap Z dlnode) : Prop :=
  map_Forall (fun (a : Z) (n : dlnode) => rw_cells rsegs m a (DLnodeCells n)) ls.

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
Lemma RBcells_lookup : forall m ns a n, RBcells m ns -> ns !! a = Some n -> exists pad, rw_cells rsegs m a (RBnodeCells n pad).
Proof. intros m ns a n H L. exact (map_Forall_lookup_1 _ _ _ _ H L). Qed.
Lemma DLcells_lookup : forall m ls a n, DLcells m ls -> ls !! a = Some n -> rw_cells rsegs m a (DLnodeCells n).
Proof. intros m ls a n H L. exact (map_Forall_lookup_1 _ _ _ _ H L). Qed.

End RBL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KIT.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma rw_cells_recells : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[WF B] W] WF' EB ES. split; [split|].
  - exact WF'.
  - rewrite EB. exact B.
  - rewrite ES. exact W.
Qed.

(* [comment removed for export] *)
Lemma PMutex_of_zero : forall m a, rw_cells rsegs m a PMutexZeroCells -> a mod 4 = 0 -> PMutex m a 0.
Proof.
  intros m a H Ha. split; [| split; [left; reflexivity| exact Ha]].
  eapply rw_cells_recells; [exact H | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.
Lemma PCond_of_zero6 : forall m a, rw_cells rsegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> a mod 8 = 0 -> PCond m a 0.
Proof.
  intros m a H Ha. split; [| split; [left; reflexivity| exact Ha]].
  eapply rw_cells_recells; [exact H | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma le8_firstn4 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Lemma C8_read_low4 : forall m A (w : word) cs,
  rw_cells rsegs m A (C8 w :: cs) -> ov_read_bytes rsegs m (wa A) 4 = Some (le4 w).
Proof.
  intros m A w cs [[WF B] _].
  pose proof (bytes_at_ov_read rsegs m A _ 0 4 B) as R. rewrite Z.add_0_r in R.
  rewrite R. 2:{ cbn [cells_bytes cbytes app length]. rewrite length_app, length_le8. lia. }
  cbn [cells_bytes cbytes skipn]. rewrite firstn_app, length_le8. cbn [Nat.sub firstn]. rewrite app_nil_r. rewrite le8_firstn4. reflexivity.
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

Lemma PMutex_transport : forall W m m' a lk,
  PMutex m a lk -> munch W m m' -> wmono rsegs m m' -> disjoint_from W a SZ_PMUTEX -> PMutex m' a lk.
Proof.
  intros W m m' a lk (C & L & A) MU WM D. split; [| split; assumption].
  unfold PMutexCells, zeros, SZ_PMUTEX in *. xtransport MU WM D.
Qed.

Lemma PCond_transport : forall W m m' a clk,
  PCond m a clk -> munch W m m' -> wmono rsegs m m' -> disjoint_from W a SZ_PCOND -> PCond m' a clk.
Proof.
  intros W m m' a clk (C & L & A) MU WM D. split; [| split; assumption].
  unfold PCondCells, zeros, SZ_PCOND in *. xtransport MU WM D.
Qed.

Lemma ErrCode_transport : forall W m m' a E,
  ErrCode m a E -> munch W m m' -> wmono rsegs m m' -> disjoint_from W a SZ_EC -> ErrCode m' a E.
Proof.
  intros W m m' a E (C & OK) MU WM D. split; [| exact OK]. unfold ErrCodeCells, SZ_EC in *. xtransport MU WM D.
Qed.
Scheme kc__3 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.

Lemma HttpCat_transport : forall W m m' b,
  HttpCat m b -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W G_HTTP_CAT 56 -> disjoint_from W G_HTTP_CAT_GUARD 8 -> HttpCat m' b.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RMalloc_iface_stmt.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Init.Datatypes.bool); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.HttpCat); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.RSegs.rsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.G_HTTP_CAT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.HttpCatCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.G_HTTP_CAT_GUARD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.HttpCatGuardCells); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@kc__3); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XRep.KIT.disjoint_from_sub); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.false)|] [|@C2; @C1; @b; @__ff; @__varmap; @__wit; @__x1; @__arith; @x; @y; @m; @n; @D2; @D1; @WM; @MU; @H; @m'; @W|] "#%t#2#t#S#B#D#A###$#'#/#(#1#%#0#&#[#Q#j#h#*#=#M#\#;#+#)#.#_#Z#`#s#5#9#8#F#G#H#K#J#-#U#r#o#m#u#t#i#N#v#,#6#<#T#V#W#Y#^#a#e#d#f#g#b#l#n#p#q#L#?#7#k#@#:#c#C#E#I#R#P#O#>#]#X3#g$#h'#3%#2%#i$#j%#1$#k$#l$#m&#n$#o+#p-#q%#r'#s*US0SC'S('#'#'#'#'#US1#US2#US1(US2#USD#k##&#0MG*H$FOD#+H$FOE#VS3%#WS4KIOWS5FKIUS6S(US6#'#'#'#US7#,S$D#US7;,S)E#0S$S*k##$#k##'#k##/#k##1#j##3#+M$FIE#*O$FKD#+I$FS*E#WS4S)S$S*WS5FS)S$,S8D4,S+E3*G$FJD#$FNEB*M$FND#$FNE1VS3$#k#$'#k#%)#j#&S%#*S&$FS+D#+S&$FJE#$FJD&-')#USES9US0S9VSFCHUSGCUSHCVSICS(1C#S,#2%S-PPS'#S.VSJ&S'(S%S&VSKGMWSLS%#S&m$%#WSMCSNHXSOGM$#l#'*)#l#(0/#l#)32#j#*C#%GGk#*C#UGDl#+&$#%DDm#$##SP##############################################################################################################)#&D#&Ds#z%$#%$$j#,CG%HGUSQ#j#-C#j#,C#&HGXSRCCSS#(C#j#.C#j#/C#(CD)G(C#j#,S/#(Cs$/`S:S/CCCQQ11$7s$0#fS;CCCCCCR222R)DD(7s$1#(C6`S<CCS#4S#087$77#VS=Cs$4WS>Cs#g#1C#S,#2s#jS-PPS'#S.l#'#s#gs#al#(s#ns#m#l#)s#qs#p#j#*C#&Gs$<%##k#*C#l#+&#s#aXS?s##B/#&Ds#y%#s#&m#%#.LDs$DDs#|Os#c#/FLNJDs$'HKI#-s$&)#UGEl#+s#ns#l#%EEm#$#)s#c&E#&Es$L%$#%$$(CE(Cs$P`S:S/CCCQQs#4s#4s#'s#js$Q#fS;CCCCCCRs#5s#5s#5Rs#,EE%*s$R#(C)`S<CCS#s#7S#s#3+*$**#VS=Cs$UWS>Cs$.#1C#S,#2s$1S-PPS'#S.l#'#s$.s$(l#(s$5s$4#l#)s$8s$7#j#*C#&Gs$]%##k#*C#l#+&#<XS?65/#&E?%#9m#%#.LEs$eEBM>#/FLNJEs$HGKI#XS@s$Gs$Hs#&#j#$s$I#j#%s$L#*SA$FS+D#+SA$FJE#$FJD&-')#&D#%#s#Xm#s#7#.LDs$vD&Os$9#/FLNJD-HKI#-,)#&E#%#s#/m#;#.LEs${E&Ms#4#/FLNJE2GKI#XS@12*#j#$3#j#%6#XSTs$e9#SBV#KI0S8SBm#$#j#0s$s#j#1s$u#j#2s$w#j#3s$y#j#$s${#j#%s$~#V#HGj##s%&#j##s%=#YSUs%>s%<s%*#Gj#4s%A#j#&S%#j#5s%D#j#.SV#j#6s%R##"). Qed.

Lemma FlatBuf_transport : forall W LB m m' a F ds,
  FlatBuf LB m a F ds -> munch W m m' -> wmono rsegs m m' -> disjoint_from W a SZ_FB ->
  (F <> FB_empty -> disjoint_from W (fb_begin F) (fb_cap F)) -> FlatBuf LB m' a F ds.
Proof.
  intros W LB m m' a F ds (C & OK & L & DATA) MU WM D DB. split; [| split; [exact OK| split; [exact L|]]].
  - unfold FlatBufCells, SZ_FB in *. xtransport MU WM D.
  - intros NE. destruct (DATA NE) as (pre & junk & CD). exists pre, junk.
    destruct OK as [E|(p & IN & RB & CAP & O1 & O2)]; [contradiction|].
    pose proof (rw_cells_bound _ _ _ _ CD) as B. cbn [cells_size csize Nat.add] in B.
    destruct CD as [[WF BA] WR]. cbn in WF.
    eapply rw_cells_transport; [ split; [split; [exact WF| exact BA] | exact WR] | exact MU | exact WM |].
    eapply disjoint_from_sub; [exact (DB NE) | lia |].
    cbn [cells_size csize Nat.add]. unfold fb_cap, fb_size, zlength in *. lia.
Qed.

Lemma AllocImpl_transport : forall W LB m m' a,
  AllocImpl LB m a -> munch W m m' -> wmono rsegs m m' -> disjoint_from W a SZ_ALLOCIMPL -> AllocImpl LB m' a.
Proof.
  intros W LB m m' a (p & junk & IN & C) MU WM D. exists p, junk. split; [exact IN|]. unfold SZ_ALLOCIMPL in *. xtransport MU WM D.
Qed.

Lemma Registry_transport : forall W LB m m' r owner first lk,
  Registry LB m r owner first lk -> munch W m m' -> wmono rsegs m m' -> disjoint_from W r NEWSZ_REG ->
  Registry LB m' r owner first lk.
Proof.
  intros W LB m m' r owner first lk (p & j0 & j7 & IN & C0 & PM & C1 & C2) MU WM D. exists p, j0, j7.
  unfold NEWSZ_REG, O_REG_MUTEX, O_REG_OWNER, SZ_REG, CookieCells, zeros in *.
  split; [exact IN|]. split; [xtransport MU WM D|]. split.
  { eapply PMutex_transport; [exact PM| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PMUTEX; lia]]. }
  split; xtransport MU WM D.
Qed.

Lemma ConfigSvc_transport : forall W LB m m' c S,
  ConfigSvc LB m c S -> munch W m m' -> wmono rsegs m m' -> disjoint_from W c NEWSZ_CFG -> ConfigSvc LB m' c S.
Proof.
  intros W LB m m' c S (p & j4 & j7 & IN & C & E) MU WM D. exists p, j4, j7. split; [exact IN|]. split; [| exact E].
  unfold NEWSZ_CFG, SvcHdrCells, CookieCells, zeros in *. xtransport MU WM D.
Qed.

Lemma StreamSvc_transport : forall W LB m m' v S implb,
  StreamSvc LB m v S implb -> munch W m m' -> wmono rsegs m m' -> disjoint_from W v NEWSZ_SSVC -> StreamSvc LB m' v S implb.
Proof.
  intros W LB m m' v S implb (p & j7 & IN & C & E) MU WM D. exists p, j7. split; [exact IN|]. split; [| exact E].
  unfold NEWSZ_SSVC, SvcHdrCells, CookieCells, zeros in *. xtransport MU WM D.
Qed.

Lemma Scheduler_transport : forall W LB m m' s S,
  Scheduler LB m s S -> munch W m m' -> wmono rsegs m m' -> disjoint_from W s NEWSZ_SCH -> Scheduler LB m' s S.
Proof.
  intros W LB m m' s S (p & j50 & jm & j109 & je & jt & j219 & j7 & IN & C0 & C1 & C2 & PM & C3 & C4 & PC & C5 & C6 & E) MU WM D.
  exists p, j50, jm, j109, je, jt, j219, j7.
  unfold NEWSZ_SCH, SZ_SCH, O_SCH_ONE_THREAD, O_SCH_MUTEX, O_SCH_PMUTEX, O_SCH_SPIN, O_SCH_EVENT, O_SCH_COND, O_SCH_EVSTATE,
         SvcHdrCells, CookieCells, zeros in *.
  split; [exact IN|]. split; [xtransport MU WM D|]. split; [xtransport MU WM D|]. split; [xtransport MU WM D|].
  split. { eapply PMutex_transport; [exact PM| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PMUTEX; lia]]. }
  split; [xtransport MU WM D|]. split; [xtransport MU WM D|].
  split. { eapply PCond_transport; [exact PC| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PCOND; lia]]. }
  split; [xtransport MU WM D|]. split; [xtransport MU WM D| exact E].
Qed.

Lemma ImplBlock_transport : forall W LB m m' b I,
  ImplBlock LB m b I -> munch W m m' -> wmono rsegs m m' -> disjoint_from W b SZ_SPCI_IMPL ->
  (0 < im_vcap I -> disjoint_from W (im_vb I) (8 * im_vcap I)) -> ImplBlock LB m' b I.
Proof.
  intros W LB m m' b I (p & j7 & IN & RB & CH & OK & EV & PM & CV & LE & ST) MU WM D DV. exists p, j7.
  unfold SZ_SPCI_IMPL, O_SPC_STORAGE, O_IMPL_MUTEX, O_IMPL_VEC_BEGIN, SpcHdrCells in *.
  split; [exact IN|]. split; [exact RB|]. split; [xtransport MU WM D|]. split; [exact OK|]. split; [exact EV|].
  split. { eapply PMutex_transport; [exact PM| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PMUTEX; lia]]. }
  split; [xtransport MU WM D|]. split; [exact LE|].
  destruct ST as [ST|(q & junk & INq & RBq & POS & CS)]; [left; exact ST| right]. exists q, junk.
  split; [exact INq|]. split; [exact RBq|]. split; [exact POS|].
  pose proof (rw_cells_bound _ _ _ _ CS) as B. destruct CS as [[WF BA] WR].
  eapply rw_cells_transport; [ split; [split; [exact WF| exact BA] | exact WR] | exact MU | exact WM |].
  eapply disjoint_from_sub; [exact (DV POS) | lia |].
  cbn [cells_size csize Nat.add] in *. cbn in WF. unfold zlength in *. lia.
Qed.

Lemma StateBlock_transport : forall W LB m m' b ioc implb S ds,
  StateBlock LB m b ioc implb S ds -> munch W m m' -> wmono rsegs m m' -> disjoint_from W b SZ_SPCI_STATE ->
  (st_fb S <> FB_empty -> disjoint_from W (fb_begin (st_fb S)) (fb_cap (st_fb S))) -> StateBlock LB m' b ioc implb S ds.
Proof.
  intros W LB m m' b ioc implb S ds (p & j7 & j16 & j4 & IN & RB & CH & OK & EV & CE & CW & PM & FB & PC & CO & E) MU WM D DF.
  exists p, j7, j16, j4.
  unfold SZ_SPCI_STATE, O_ST_EXEC, O_ST_WP_PX, O_ST_MUTEX, O_ST_FB, O_ST_CV, O_ST_OP, SpcHdrCells, AnyExecCells in *.
  split; [exact IN|]. split; [exact RB|]. split; [xtransport MU WM D|]. split; [exact OK|]. split; [exact EV|].
  split; [xtransport MU WM D|]. split; [xtransport MU WM D|].
  split. { eapply PMutex_transport; [exact PM| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PMUTEX; lia]]. }
  split. { eapply FlatBuf_transport; [exact FB| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_FB; lia]| exact DF]. }
  split. { eapply PCond_transport; [exact PC| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PCOND; lia]]. }
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
