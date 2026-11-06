(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr Frame.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_FUZZ                       : Z := 0x2c280.   (* [comment removed for export] *)
Definition P_STREAM_CTOR                : Z := 0x2c544.   (* [comment removed for export] *)
Definition P_STREAM_CLOSE_REMOTE        : Z := 0x2c6e4.   (* [comment removed for export] *)
Definition P_PARSER_DTOR                : Z := 0x2c7fc.   (* [comment removed for export] *)
Definition P_STREAM_DTOR                : Z := 0x2c8e0.   (* [comment removed for export] *)
Definition P_ECAT_FAILED                : Z := 0x2cb68.   (* [comment removed for export] *)
Definition P_MAKE_SVC_CONFIG            : Z := 0x2d06c.   (* [comment removed for export] *)
Definition P_DESTROY_ALLOC_CONFIG       : Z := 0x2d230.   (* [comment removed for export] *)
Definition P_CONFIG_SHUTDOWN            : Z := 0x2d2c8.   (* [comment removed for export] *)
Definition P_CONFIG_GET_VALUE           : Z := 0x2d2d0.   (* [comment removed for export] *)
Definition P_DEALLOC_OBJ_CONFIG         : Z := 0x2d490.   (* [comment removed for export] *)
Definition P_DO_ADD_SERVICE             : Z := 0x2d4e8.   (* [comment removed for export] *)
Definition P_THROW_INVALID_SERVICE_OWNER : Z := 0x2d668.   (* [comment removed for export] *)
Definition P_THROW_SERVICE_ALREADY_EXISTS : Z := 0x2d6d0.   (* [comment removed for export] *)
Definition P_DESTROY_ADDED              : Z := 0x2d738.   (* [comment removed for export] *)
Definition P_STD_THROW_BAD_ARRAY_NEW_LENGTH : Z := 0x2e238.   (* [comment removed for export] *)
Definition P_ALLOCIMPL_DESTROY          : Z := 0x2e280.   (* [comment removed for export] *)
Definition P_ALLOCIMPL_ALLOCATE         : Z := 0x2e2b8.   (* [comment removed for export] *)
Definition P_ALLOCIMPL_DEALLOCATE       : Z := 0x2e3a8.   (* [comment removed for export] *)
Definition P_ALLOCIMPL_BASE_DTOR        : Z := 0x2e448.   (* [comment removed for export] *)
Definition P_THROW_BAD_ALLOC            : Z := 0x2e454.   (* [comment removed for export] *)
Definition P_ALLOC_OBJ_REGISTRY         : Z := 0x2e8cc.   (* [comment removed for export] *)
Definition P_THROW_SYSTEM_ERROR         : Z := 0x2ecac.   (* [comment removed for export] *)
Definition P_MAKE_SVC_SCHED             : Z := 0x2f700.   (* [comment removed for export] *)
Definition P_ALLOC_OBJ_SCHED            : Z := 0x2f808.   (* [comment removed for export] *)
Definition P_DESTROY_ALLOC_SCHED        : Z := 0x2f8cc.   (* [comment removed for export] *)
Definition P_SCHED_GET_DEFAULT_TASK     : Z := 0x2f914.   (* [comment removed for export] *)
Definition P_SCHED_CTOR                 : Z := 0x2f944.   (* [comment removed for export] *)
Definition P_DO_USE_SERVICE             : Z := 0x2fcf0.   (* [comment removed for export] *)
Definition P_CREATE_CONFIG              : Z := 0x30e6c.   (* [comment removed for export] *)
Definition P_CONFIG_GET_BOOL            : Z := 0x31014.   (* [comment removed for export] *)
Definition P_THROW_OUT_OF_RANGE         : Z := 0x310e0.   (* [comment removed for export] *)
Definition P_CONFIG_GET_INT             : Z := 0x315a0.   (* [comment removed for export] *)
Definition P_OPQUEUE_DTOR               : Z := 0x320e4.   (* [comment removed for export] *)
Definition P_CEM_SCOPED_LOCK            : Z := 0x32158.   (* [comment removed for export] *)
Definition P_CEM_CTOR                   : Z := 0x32670.   (* [comment removed for export] *)
Definition P_SCHED_DTOR                 : Z := 0x327c4.   (* [comment removed for export] *)
Definition P_SCHED_DELDTOR              : Z := 0x328d0.   (* [comment removed for export] *)
Definition P_SCHED_SHUTDOWN             : Z := 0x328fc.   (* [comment removed for export] *)
Definition P_POSIX_EVENT_CTOR           : Z := 0x32a44.   (* [comment removed for export] *)
Definition P_CONFIG_GET_LONG            : Z := 0x32b60.   (* [comment removed for export] *)
Definition P_POSIX_EVENT_SIGNAL_ALL     : Z := 0x333b0.   (* [comment removed for export] *)
Definition P_DEALLOC_OBJ_SCHED          : Z := 0x33bcc.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_PARSER_DTOR_THUNK          : Z := 0x33c54.   (* [comment removed for export] *)
Definition P_ON_REQUEST_IMPL            : Z := 0x33c80.   (* [comment removed for export] *)
Definition P_ON_RESPONSE_IMPL           : Z := 0x33c9c.   (* [comment removed for export] *)
Definition P_ON_FIELD_IMPL              : Z := 0x33ca0.   (* [comment removed for export] *)
Definition P_ON_TRAILER_FIELD_IMPL      : Z := 0x33ca8.   (* [comment removed for export] *)
Definition P_ON_HEADER_IMPL             : Z := 0x33de0.   (* [comment removed for export] *)
Definition P_ON_BODY_INIT_IMPL          : Z := 0x33df0.   (* [comment removed for export] *)
Definition P_ON_BODY_IMPL               : Z := 0x33e08.   (* [comment removed for export] *)
Definition P_ON_CHUNK_HEADER_IMPL       : Z := 0x33e34.   (* [comment removed for export] *)
Definition P_ON_CHUNK_BODY_IMPL         : Z := 0x33e70.   (* [comment removed for export] *)
Definition P_ON_FINISH_IMPL             : Z := 0x33ec8.   (* [comment removed for export] *)
Definition P_FIELDS_DTOR                : Z := 0x33ed8.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_FIELDS_DELETE_LIST         : Z := 0x33f84.   (* [comment removed for export] *)
Definition P_FIELDS_REALLOC_STRING      : Z := 0x33fec.   (* [comment removed for export] *)
Definition P_SV_COPY                    : Z := 0x34090.   (* [comment removed for export] *)
Definition P_ON_REQUEST_IMPL_T          : Z := 0x34290.   (* [comment removed for export] *)
Definition P_EC_CTOR_HTTP               : Z := 0x34360.   (* [comment removed for export] *)
Definition P_HEADER_SET_METHOD          : Z := 0x3444c.   (* [comment removed for export] *)
Definition P_HEADER_SET_VERSION         : Z := 0x3454c.   (* [comment removed for export] *)
Definition P_FIELDS_REALLOC_TARGET      : Z := 0x34728.   (* [comment removed for export] *)
Definition P_STRING_TO_VERB             : Z := 0x34cdc.   (* [comment removed for export] *)
Definition P_SV_INDEX                   : Z := 0x35498.   (* [comment removed for export] *)
Definition P_SV_REMOVE_PREFIX           : Z := 0x354fc.   (* [comment removed for export] *)
Definition P_FIELDS_INSERT              : Z := 0x35568.   (* [comment removed for export] *)
Definition P_FIELDS_NEW_ELEMENT         : Z := 0x355ec.   (* [comment removed for export] *)
Definition P_FIELDS_INSERT_ELEMENT      : Z := 0x35790.   (* [comment removed for export] *)
Definition P_FIELDS_VALUE_TYPE_CTOR     : Z := 0x35a24.   (* [comment removed for export] *)
Definition P_LIST_ITERATOR_TO           : Z := 0x35b60.   (* [comment removed for export] *)
Definition P_RB_UPPER_BOUND_LOOP        : Z := 0x35bac.   (* [comment removed for export] *)
Definition P_KEY_COMPARE_SV_VT          : Z := 0x35c38.   (* [comment removed for export] *)
Definition P_FIELDS_FIND_SV             : Z := 0x35d38.   (* [comment removed for export] *)
Definition P_LIST_ITERATOR_TO_C         : Z := 0x35db0.   (* [comment removed for export] *)
Definition P_RB_FIND                    : Z := 0x35dfc.   (* [comment removed for export] *)
Definition P_RB_LOWER_BOUND_LOOP        : Z := 0x35e9c.   (* [comment removed for export] *)
Definition P_KEY_COMPARE_VT_SV          : Z := 0x35f28.   (* [comment removed for export] *)
Definition P_RB_INSERT_BEFORE           : Z := 0x35fb4.   (* [comment removed for export] *)
Definition P_RB_REBALANCE               : Z := 0x36014.   (* [comment removed for export] *)
Definition P_RB_INSERT_COMMIT           : Z := 0x36234.   (* [comment removed for export] *)
Definition P_RB_PREV_NODE               : Z := 0x36304.   (* [comment removed for export] *)
Definition P_RB_IS_HEADER               : Z := 0x363d0.   (* [comment removed for export] *)
Definition P_FIELDS_INDEX_F             : Z := 0x3664c.   (* [comment removed for export] *)
Definition P_TOKEN_LIST_EXISTS          : Z := 0x366e8.   (* [comment removed for export] *)
Definition P_FIELDS_FIND_F              : Z := 0x367dc.   (* [comment removed for export] *)
Definition P_FIELD_TABLE_CTOR           : Z := 0x368ec.   (* [comment removed for export] *)
Definition P_FIELD_TABLE_DIGEST         : Z := 0x36a0c.   (* [comment removed for export] *)
Definition P_TOKEN_LIST_ITER_INCR       : Z := 0x36ca0.   (* [comment removed for export] *)
Definition P_TOKEN_LIST_ITER_CTOR       : Z := 0x36dd4.   (* [comment removed for export] *)
Definition P_READER_PUT                 : Z := 0x36ef0.   (* [comment removed for export] *)
Definition P_MB_DYN_PREPARE             : Z := 0x37084.   (* [comment removed for export] *)
Definition P_MB_COMMIT                  : Z := 0x37154.   (* [comment removed for export] *)
Definition P_MB_PREPARE                 : Z := 0x37260.   (* [comment removed for export] *)
Definition P_MB_LIST_ITERATOR_TO        : Z := 0x37734.   (* [comment removed for export] *)
Definition P_MB_ALLOC                   : Z := 0x377e8.   (* [comment removed for export] *)
Definition P_MB_SUBRANGE_CTOR           : Z := 0x3789c.   (* [comment removed for export] *)
Definition P_MB_SUBRANGE_DEREF          : Z := 0x37fd0.   (* [comment removed for export] *)
Definition P_BUFFER_COPY_MB             : Z := 0x38098.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_STD_THROW_LENGTH_ERROR     : Z := 0x3833c.   (* [comment removed for export] *)
Definition P_SSVC_MAKE_IMPL             : Z := 0x383a4.   (* [comment removed for export] *)
Definition P_SP_STATE_ARROW             : Z := 0x384e0.   (* [comment removed for export] *)
Definition P_FB_PREPARE                 : Z := 0x38524.   (* [comment removed for export] *)
Definition P_MAKE_SHARED_STATE          : Z := 0x38788.   (* [comment removed for export] *)
Definition P_SP_IMPL_ARROW              : Z := 0x38924.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_ANYEX_QUERY_CONTEXT        : Z := 0x38968.   (* [comment removed for export] *)
Definition P_THROW_BAD_EXECUTOR         : Z := 0x38a08.   (* [comment removed for export] *)
Definition P_CREATE_SSVC                : Z := 0x38ef8.   (* [comment removed for export] *)
Definition P_ALLOC_OBJ_SSVC             : Z := 0x38f44.   (* [comment removed for export] *)
Definition P_DESTROY_ALLOC_SSVC         : Z := 0x39000.   (* [comment removed for export] *)
Definition P_MAKE_SHARED_IMPL           : Z := 0x39088.   (* [comment removed for export] *)
Definition P_SSVC_DTOR                  : Z := 0x39154.   (* [comment removed for export] *)
Definition P_SSVC_DELDTOR               : Z := 0x3916c.   (* [comment removed for export] *)
Definition P_SSVC_SHUTDOWN              : Z := 0x391a8.   (* [comment removed for export] *)
Definition P_NONCOPYABLE_DTOR           : Z := 0x39388.   (* [comment removed for export] *)
Definition P_SHCOUNT_CTOR_IMPL          : Z := 0x3938c.   (* [comment removed for export] *)
Definition P_SHCOUNT_DTOR               : Z := 0x39410.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_DTOR             : Z := 0x394a4.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_DELDTOR          : Z := 0x394bc.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_DISPOSE          : Z := 0x394f8.   (* [comment removed for export] *)
Definition P_SPCB_DESTROY               : Z := 0x39500.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_GET_DEL          : Z := 0x3950c.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_GET_LDEL         : Z := 0x39530.   (* [comment removed for export] *)
Definition P_SPCI_IMPL_GET_UDEL         : Z := 0x39538.   (* [comment removed for export] *)
Definition P_SPMSD_IMPL_DESTROY         : Z := 0x39540.   (* [comment removed for export] *)
Definition P_VEC_READOP_RESERVE         : Z := 0x395e8.   (* [comment removed for export] *)
Definition P_VEC_READOP_THROW_LEN       : Z := 0x3966c.   (* [comment removed for export] *)
Definition P_SPLITBUF_READOP_DTOR       : Z := 0x3980c.   (* [comment removed for export] *)
Definition P_ALLOC_AT_LEAST_READOP      : Z := 0x39860.   (* [comment removed for export] *)
Definition P_VEC_READOP_DESTROY         : Z := 0x39a08.   (* [comment removed for export] *)
Definition P_DEALLOC_OBJ_SSVC           : Z := 0x39b00.   (* [comment removed for export] *)
Definition P_SHCOUNT_CTOR_STATE         : Z := 0x39b58.   (* [comment removed for export] *)
Definition P_SPCI_STATE_DTOR            : Z := 0x39bdc.   (* [comment removed for export] *)
Definition P_SPCI_STATE_DELDTOR         : Z := 0x39c2c.   (* [comment removed for export] *)
Definition P_SPCI_STATE_DISPOSE         : Z := 0x39c80.   (* [comment removed for export] *)
Definition P_SPCI_STATE_GET_DEL         : Z := 0x39cc4.   (* [comment removed for export] *)
Definition P_SPCI_STATE_GET_LDEL        : Z := 0x39ce8.   (* [comment removed for export] *)
Definition P_SPCI_STATE_GET_UDEL        : Z := 0x39cf0.   (* [comment removed for export] *)
Definition P_STATE_DTOR                 : Z := 0x39cf8.   (* [comment removed for export] *)
Definition P_ANYEX_COPY                 : Z := 0x39e20.   (* [comment removed for export] *)
Definition P_ANYEX_MOVE                 : Z := 0x39e78.   (* [comment removed for export] *)
Definition P_SPLITBUF_STATEP_DTOR       : Z := 0x3a504.   (* [comment removed for export] *)
Definition P_VEC_STATEP_THROW_LEN       : Z := 0x3a550.   (* [comment removed for export] *)
Definition P_ALLOC_AT_LEAST_STATEP      : Z := 0x3a568.   (* [comment removed for export] *)
Definition P_ANYEX_FN_DESTROY           : Z := 0x3afc0.   (* [comment removed for export] *)
Definition P_ANYEX_FN_COPY              : Z := 0x3afc4.   (* [comment removed for export] *)
Definition P_ANYEX_FN_MOVE              : Z := 0x3afd4.   (* [comment removed for export] *)
Definition P_ANYEX_FN_TARGET            : Z := 0x3afe4.   (* [comment removed for export] *)
Definition P_ANYEX_FN_QUERY_CTX         : Z := 0x3afe8.   (* [comment removed for export] *)
Definition P_STREAM_CLOSE               : Z := 0x3c43c.   (* [comment removed for export] *)
Definition P_STATE_REMOVE               : Z := 0x3c694.   (* [comment removed for export] *)
Definition P_SYNC_READ_OP               : Z := 0x3c8a0.   (* [comment removed for export] *)
Definition P_HTTP_READ_SOME             : Z := 0x3c95c.   (* [comment removed for export] *)
Definition P_FB_DYN_PREPARE             : Z := 0x3cd44.   (* [comment removed for export] *)
Definition P_STREAM_READ_SOME           : Z := 0x3ce20.   (* [comment removed for export] *)
Definition P_BP_PUT_EOF                 : Z := 0x3d32c.   (* [comment removed for export] *)
Definition P_BP_PUT                     : Z := 0x3d448.   (* [comment removed for export] *)
Definition P_BP_PARSE_START_LINE        : Z := 0x3d860.   (* [comment removed for export] *)
Definition P_BP_PARSE_FIELDS            : Z := 0x3d968.   (* [comment removed for export] *)
Definition P_BP_FINISH_HEADER           : Z := 0x3da6c.   (* [comment removed for export] *)
Definition P_BP_CONTENT_LENGTH          : Z := 0x3dc3c.   (* [comment removed for export] *)
Definition P_BP_PARSE_BODY              : Z := 0x3dca8.   (* [comment removed for export] *)
Definition P_BP_PARSE_BODY_TO_EOF       : Z := 0x3dd98.   (* [comment removed for export] *)
Definition P_BP_PARSE_CHUNK_HEADER      : Z := 0x3de70.   (* [comment removed for export] *)
Definition P_BP_INNER_PARSE_START_LINE  : Z := 0x3e3c8.   (* [comment removed for export] *)
Definition P_BP_PARSE_VERSION           : Z := 0x3e844.   (* [comment removed for export] *)
Definition P_BP_INNER_PARSE_FIELDS      : Z := 0x3eb28.   (* [comment removed for export] *)
Definition P_BP_PARSE_FIELD             : Z := 0x3ee14.   (* [comment removed for export] *)
Definition P_BP_DO_FIELD                : Z := 0x3f39c.   (* [comment removed for export] *)
Definition P_BP_PARSE_TOKEN_TO_EOL      : Z := 0x3fbc8.   (* [comment removed for export] *)
Definition P_STRING_TO_FIELD            : Z := 0x3fd28.   (* [comment removed for export] *)
Definition P_FIELD_TABLE_EQUALS         : Z := 0x3fe04.   (* [comment removed for export] *)
Definition P_VALIDATE_OPT_TOKEN_LIST    : Z := 0x3ff2c.   (* [comment removed for export] *)
Definition P_BP_DO_FIELD_LAMBDA         : Z := 0x3ffe0.   (* [comment removed for export] *)
Definition P_OPT_TOKEN_LIST_INCR        : Z := 0x402a8.   (* [comment removed for export] *)
Definition P_BP_PARSE_CHUNK_EXT         : Z := 0x40464.   (* [comment removed for export] *)
Definition P_EC_ASSIGN_HTTP             : Z := 0x4080c.   (* [comment removed for export] *)
Definition P_READ_SIZE_FB               : Z := 0x408f0.   (* [comment removed for export] *)
Definition P_CXA_GUARD_ACQUIRE          : Z := 0x409fc.   (* [comment removed for export] *)
Definition P_CXA_GUARD_RELEASE          : Z := 0x40a4c.   (* [comment removed for export] *)
Definition P_STD_TERMINATE              : Z := 0x40a7c.   (* [comment removed for export] *)
Definition P_OPDEL                      : Z := 0x5d2d8.   (* [comment removed for export] *)
Definition P_OPDEL2                     : Z := 0x5d2dc.   (* [comment removed for export] *)
Definition P_OPDEL_ARR                  : Z := 0x5d2e0.   (* [comment removed for export] *)
Definition P_STD_ALIGN                  : Z := 0x5ebdc.   (* [comment removed for export] *)
Definition P_STD_THROW_SYSTEM_ERROR     : Z := 0x62bd8.   (* [comment removed for export] *)
Definition P_CV_DTOR                    : Z := 0x62d3c.   (* [comment removed for export] *)
Definition P_CV_NOTIFY_ALL              : Z := 0x62d74.   (* [comment removed for export] *)
Definition P_CV_WAIT                    : Z := 0x62d90.   (* [comment removed for export] *)
Definition P_MTX_DTOR                   : Z := 0x62f0c.   (* [comment removed for export] *)
Definition P_MTX_LOCK                   : Z := 0x62f28.   (* [comment removed for export] *)
Definition P_MTX_UNLOCK                 : Z := 0x62f70.   (* [comment removed for export] *)
Definition P_ERRNO_LOCATION             : Z := 0x6b898.   (* [comment removed for export] *)
Definition P_ASSERT_FAIL                : Z := 0x6b990.   (* [comment removed for export] *)
Definition P_FREE                       : Z := 0x6c204.   (* [comment removed for export] *)
Definition P_MALLOC                     : Z := 0x6c344.   (* [comment removed for export] *)
Definition P_TOWRITE                    : Z := 0x6ee40.   (* [comment removed for export] *)
Definition P_FWRITEX                    : Z := 0x6f038.   (* [comment removed for export] *)
Definition P_SNPRINTF                   : Z := 0x6f264.   (* [comment removed for export] *)
Definition P_VFPRINTF                   : Z := 0x6f58c.   (* [comment removed for export] *)
Definition P_PRINTF_CORE                : Z := 0x6f73c.   (* [comment removed for export] *)
Definition P_POP_ARG                    : Z := 0x7056c.   (* [comment removed for export] *)
Definition P_PAD                        : Z := 0x706a0.   (* [comment removed for export] *)
Definition P_VSNPRINTF                  : Z := 0x73fc4.   (* [comment removed for export] *)
Definition P_SN_WRITE                   : Z := 0x74090.   (* [comment removed for export] *)
Definition P_SHLIM                      : Z := 0x75758.   (* [comment removed for export] *)
Definition P_SHGETC                     : Z := 0x75790.   (* [comment removed for export] *)
Definition P_STRTOLL                    : Z := 0x783e8.   (* [comment removed for export] *)
Definition P_INTSCAN                    : Z := 0x78608.   (* [comment removed for export] *)
Definition P_BCMP                       : Z := 0x79450.   (* [comment removed for export] *)
Definition P_MEMCHR                     : Z := 0x79454.   (* [comment removed for export] *)
Definition P_MEMCMP                     : Z := 0x79520.   (* [comment removed for export] *)
Definition P_MEMCPY                     : Z := 0x79550.   (* [comment removed for export] *)
Definition P_MEMMOVE                    : Z := 0x79954.   (* [comment removed for export] *)
Definition P_MEMSET                     : Z := 0x79ad0.   (* [comment removed for export] *)
Definition P_STRCMP                     : Z := 0x79bc8.   (* [comment removed for export] *)
Definition P_STRLEN                     : Z := 0x79c98.   (* [comment removed for export] *)
Definition P_PTHREAD_COND_BROADCAST     : Z := 0x7a2d4.   (* [comment removed for export] *)
Definition P_PTHREAD_COND_DESTROY       : Z := 0x7a348.   (* [comment removed for export] *)
Definition P_PTHREAD_COND_INIT          : Z := 0x7a50c.   (* [comment removed for export] *)
Definition P_PRIVATE_COND_SIGNAL        : Z := 0x7acb0.   (* [comment removed for export] *)
Definition P_PTHREAD_CONDATTR_DESTROY   : Z := 0x7b140.   (* [comment removed for export] *)
Definition P_PTHREAD_CONDATTR_INIT      : Z := 0x7b148.   (* [comment removed for export] *)
Definition P_PTHREAD_CONDATTR_SETCLOCK  : Z := 0x7b154.   (* [comment removed for export] *)
Definition P_PTHREAD_MUTEX_DESTROY      : Z := 0x7c02c.   (* [comment removed for export] *)
Definition P_PTHREAD_MUTEX_INIT         : Z := 0x7c054.   (* [comment removed for export] *)
Definition P_PTHREAD_MUTEX_LOCK         : Z := 0x7c0d4.   (* [comment removed for export] *)
Definition P_PTHREAD_MUTEX_UNLOCK       : Z := 0x7c5c0.   (* [comment removed for export] *)
Definition P_VM_WAIT                    : Z := 0x7cc40.   (* [comment removed for export] *)
Definition P_OPNEW                      : Z := 0x7d324.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition RVT_ALLOCIMPL    : Z := 0x7ea68.   (* [comment removed for export] *)
Definition VP_ALLOCIMPL     : Z := 0x7ea78.
Definition VS_ALLOCIMPL_0 : Z := 0x2e280.
Definition VS_ALLOCIMPL_8 : Z := 0x2e2b8.
Definition VS_ALLOCIMPL_16 : Z := 0x2e3a8.
Definition VS_ALLOCIMPL_24 : Z := 0x2e448.
Definition VS_ALLOCIMPL_32 : Z := 0x2e44c.
Definition RVT_CONFIG_SVC   : Z := 0x7e708.   (* [comment removed for export] *)
Definition VP_CONFIG_SVC    : Z := 0x7e718.
Definition VS_CONFIG_SVC_0 : Z := 0x39388.
Definition VS_CONFIG_SVC_8 : Z := 0x2d2c0.
Definition VS_CONFIG_SVC_16 : Z := 0x2d2c8.
Definition VS_CONFIG_SVC_24 : Z := 0x2d2cc.
Definition VS_CONFIG_SVC_32 : Z := 0x2d2d0.
Definition RVT_SCHED        : Z := 0x7ee40.   (* [comment removed for export] *)
Definition VP_SCHED         : Z := 0x7ee50.
Definition VS_SCHED_0 : Z := 0x327c4.
Definition VS_SCHED_8 : Z := 0x328d0.
Definition VS_SCHED_16 : Z := 0x328fc.
Definition VS_SCHED_24 : Z := 0x2d2cc.
Definition RVT_SSVC         : Z := 0x7fbb8.   (* [comment removed for export] *)
Definition VP_SSVC          : Z := 0x7fbc8.
Definition VS_SSVC_0 : Z := 0x39154.
Definition VS_SSVC_8 : Z := 0x3916c.
Definition VS_SSVC_16 : Z := 0x391a8.
Definition VS_SSVC_24 : Z := 0x2d2cc.
Definition RVT_SPCI_IMPL    : Z := 0x7fc18.   (* [comment removed for export] *)
Definition VP_SPCI_IMPL     : Z := 0x7fc28.
Definition VS_SPCI_IMPL_0 : Z := 0x394a4.
Definition VS_SPCI_IMPL_8 : Z := 0x394bc.
Definition VS_SPCI_IMPL_16 : Z := 0x394f8.
Definition VS_SPCI_IMPL_24 : Z := 0x39500.
Definition VS_SPCI_IMPL_32 : Z := 0x3950c.
Definition VS_SPCI_IMPL_40 : Z := 0x39530.
Definition VS_SPCI_IMPL_48 : Z := 0x39538.
Definition RVT_SPCI_STATE   : Z := 0x7fc88.   (* [comment removed for export] *)
Definition VP_SPCI_STATE    : Z := 0x7fc98.
Definition VS_SPCI_STATE_0 : Z := 0x39bdc.
Definition VS_SPCI_STATE_8 : Z := 0x39c2c.
Definition VS_SPCI_STATE_16 : Z := 0x39c80.
Definition VS_SPCI_STATE_24 : Z := 0x39500.
Definition VS_SPCI_STATE_32 : Z := 0x39cc4.
Definition VS_SPCI_STATE_40 : Z := 0x39ce8.
Definition VS_SPCI_STATE_48 : Z := 0x39cf0.
Definition RVT_PARSER       : Z := 0x7ef28.   (* [comment removed for export] *)
Definition VP_PARSER        : Z := 0x7ef38.
Definition VS_PARSER_0 : Z := 0x2c7fc.
Definition VS_PARSER_8 : Z := 0x33c54.
Definition VS_PARSER_16 : Z := 0x33c80.
Definition VS_PARSER_24 : Z := 0x33c9c.
Definition VS_PARSER_32 : Z := 0x33ca0.
Definition VS_PARSER_40 : Z := 0x33ca8.
Definition VS_PARSER_48 : Z := 0x33de0.
Definition VS_PARSER_56 : Z := 0x33df0.
Definition VS_PARSER_64 : Z := 0x33e08.
Definition VS_PARSER_72 : Z := 0x33e34.
Definition VS_PARSER_80 : Z := 0x33e70.
Definition VS_PARSER_88 : Z := 0x33ec8.
Definition RVT_HTTP_ECAT    : Z := 0x7f058.   (* [comment removed for export] *)
Definition VP_HTTP_ECAT     : Z := 0x7f068.
Definition VS_HTTP_ECAT_0 : Z := 0x34598.
Definition VS_HTTP_ECAT_8 : Z := 0x345a4.
Definition VS_HTTP_ECAT_16 : Z := 0x345bc.
Definition VS_HTTP_ECAT_24 : Z := 0x345f4.
Definition VS_HTTP_ECAT_32 : Z := 0x346a4.
Definition VS_HTTP_ECAT_40 : Z := 0x346f4.
Definition VS_HTTP_ECAT_48 : Z := 0x2cb68.
Definition RVT_SYSTEM_ECAT  : Z := 0x7e518.   (* [comment removed for export] *)
Definition VP_SYSTEM_ECAT   : Z := 0x7e528.
Definition VS_SYSTEM_ECAT_0 : Z := 0x2cc18.
Definition VS_SYSTEM_ECAT_8 : Z := 0x2bfd4.
Definition VS_SYSTEM_ECAT_16 : Z := 0x2c9c4.
Definition VS_SYSTEM_ECAT_24 : Z := 0x2ca74.
Definition VS_SYSTEM_ECAT_32 : Z := 0x2cc24.
Definition VS_SYSTEM_ECAT_40 : Z := 0x2cc6c.
Definition VS_SYSTEM_ECAT_48 : Z := 0x2cb68.
Definition RVT_GENERIC_ECAT : Z := 0x7e4b8.   (* [comment removed for export] *)
Definition VP_GENERIC_ECAT  : Z := 0x7e4c8.
Definition VS_GENERIC_ECAT_0 : Z := 0x2cb70.
Definition VS_GENERIC_ECAT_8 : Z := 0x2c118.
Definition VS_GENERIC_ECAT_16 : Z := 0x2c9c4.
Definition VS_GENERIC_ECAT_24 : Z := 0x2ca74.
Definition VS_GENERIC_ECAT_32 : Z := 0x2bf8c.
Definition VS_GENERIC_ECAT_40 : Z := 0x2cb7c.
Definition VS_GENERIC_ECAT_48 : Z := 0x2cb68.
Definition RVT_MISC_ECAT    : Z := 0x7e698.   (* [comment removed for export] *)
Definition VP_MISC_ECAT     : Z := 0x7e6a8.

(* [comment removed for export] *)
Definition T_ANYEX_TARGET_FNS   : Z := 0x7fd90.   (* [comment removed for export] *)
Definition T_ANYEX_OBJECT_FNS   : Z := 0x7fe48.   (* [comment removed for export] *)
Definition T_ANYEX_PROP_FNS     : Z := 0x7fe68.   (* [comment removed for export] *)
Definition T_ANYEX_PROP_FNS_VOID : Z := 0x7fce8.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition T_ANYEX_TARGET_FNS_words : list Z := [0x3a5a4; 0x3a5b0; 0x3a68c; 0x0].
Definition T_ANYEX_OBJECT_FNS_words : list Z := [0x3afc0; 0x3afc4; 0x3afd4; 0x3afe4].
Definition T_ANYEX_PROP_FNS_words : list Z := [0x3afe8; 0x3aff0; 0x3b014; 0x3b038; 0x3b040; 0x3b090; 0x3b0e0; 0x3b0e8; 0x3b10c; 0x3b15c; 0x3b164; 0x3b188; 0x3b1a4; 0x3b1ac; 0x3b1d0; 0x3b21c; 0x3b224; 0x3b248; 0x3b298; 0x3b2a0; 0x3b2c4].
Definition T_ANYEX_PROP_FNS_VOID_words : list Z := [0x39ef0; 0x39ef4; 0x39f2c; 0x39f64; 0x39f68; 0x39fa0; 0x39fd8; 0x39fdc; 0x3a014; 0x3a04c; 0x3a050; 0x3a088; 0x3a0c0; 0x3a0c4; 0x3a0fc; 0x3a134; 0x3a138; 0x3a170; 0x3a1a8; 0x3a1ac; 0x3a1e4].

(* [comment removed for export] *)
Definition G_EXF_IN_CALLBACK      : Z := 0x94f94.   (* [comment removed for export] *)
Definition G_EXF_EMPTY            : Z := 0x94fa0.   (* [comment removed for export] *)
Definition G_ASIO_SYSTEM_CAT      : Z := 0x94fc0.   (* [comment removed for export] *)
Definition G_ASIO_NETDB_CAT       : Z := 0x94fd0.   (* [comment removed for export] *)
Definition G_ASIO_ADDRINFO_CAT    : Z := 0x94fe0.   (* [comment removed for export] *)
Definition G_ASIO_MISC_CAT        : Z := 0x94ff0.   (* [comment removed for export] *)
Definition G_CALLSTACK_TOP_GUARD  : Z := 0x95008.   (* [comment removed for export] *)
Definition G_ID_CONFIG            : Z := 0x95010.   (* [comment removed for export] *)
Definition G_ID_SCHED             : Z := 0x95020.   (* [comment removed for export] *)
Definition G_ID_REACTOR           : Z := 0x95030.   (* [comment removed for export] *)
Definition G_ID_SSVC              : Z := 0x95040.   (* [comment removed for export] *)
Definition G_HTTP_CAT             : Z := 0x95050.   (* [comment removed for export] *)
Definition G_HTTP_CAT_GUARD       : Z := 0x95088.   (* [comment removed for export] *)
Definition G_FIELD_TABLE          : Z := 0x95090.   (* [comment removed for export] *)
Definition G_FIELD_TABLE_GUARD    : Z := 0x95e08.   (* [comment removed for export] *)
Definition G_SYSTEM_CAT_INST      : Z := 0x84b98.   (* [comment removed for export] *)
Definition G_GENERIC_CAT_INST     : Z := 0x84cb0.   (* [comment removed for export] *)
Definition G_INTEROP_CAT_INST     : Z := 0x84c78.   (* [comment removed for export] *)
Definition G_MISC_CAT_INST        : Z := 0x84c40.   (* [comment removed for export] *)
Definition G_STACK_CHK_GUARD      : Z := 0xb69b0.   (* [comment removed for export] *)
Definition G_GOT_STACK_CHK        : Z := 0x83b30.   (* [comment removed for export] *)
Definition G_ERRNO                : Z := 0x968cc.   (* [comment removed for export] *)
Definition G_TP                   : Z := 0x96970.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_SYSTEM_CAT_VPTR : Z := 0x7e528.  Definition W_SYSTEM_CAT_ID : Z := 0xb2ab117a257edfd1.
Definition W_NETDB_CAT_VPTR : Z := 0x7e5e8.  Definition W_NETDB_CAT_ID : Z := 0x0.
Definition W_ADDRINFO_CAT_VPTR : Z := 0x7e648.  Definition W_ADDRINFO_CAT_ID : Z := 0x0.
Definition W_MISC_CAT_VPTR : Z := 0x7e6a8.  Definition W_MISC_CAT_ID : Z := 0x0.
Definition W_INTEROP_CAT_VPTR : Z := 0x7e588.  Definition W_INTEROP_CAT_ID : Z := 0xb2ab117a257edfd2.
Definition W_GENERIC_CAT_VPTR : Z := 0x7e4c8.  Definition W_GENERIC_CAT_ID : Z := 0xb2ab117a257edfd0.
Definition HTTP_CAT_ID : Z := 0x964627da815bf210.   (* [comment removed for export] *)
Definition CAT_ID_SYSGEN_SHR1 : Z := 0x595588bd12bf6fe8.   (* [comment removed for export] *)
Definition L_CAT_ID_SYSGEN_SHR1 : Z := 0x14e30.  Definition L_HTTP_CAT_ID : Z := 0x14ef0.
Definition TI_NAME_CONFIG : Z := 0x151a3.   (* [comment removed for export] *)
Definition TI_NAME_SCHED  : Z := 0x15491.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition L_STR_SCHEDULER          : Z := 0x10332.   (* [comment removed for export] *)
Definition L_STR_REACTOR            : Z := 0x1363e.   (* [comment removed for export] *)
Definition L_STR_IO_LOCKING         : Z := 0x147f4.   (* [comment removed for export] *)
Definition L_STR_REG_LOCKING        : Z := 0x1033c.   (* [comment removed for export] *)
Definition L_STR_CONCURRENCY_HINT   : Z := 0x132c2.   (* [comment removed for export] *)
Definition L_STR_LOCKING            : Z := 0x147ec.   (* [comment removed for export] *)
Definition L_STR_ONE                : Z := 0x12b63.   (* [comment removed for export] *)
Definition L_STR_ZERO               : Z := 0x1387e.   (* [comment removed for export] *)
Definition L_STR_MINUS_ONE          : Z := 0x108ae.   (* [comment removed for export] *)
Definition L_STR_FMT_D              : Z := 0x132d3.   (* [comment removed for export] *)
Definition L_STR_ASSUME_CONT        : Z := 0x11945.   (* [comment removed for export] *)
Definition L_STR_SPIN               : Z := 0x12da3.   (* [comment removed for export] *)
Definition L_STR_TASK_USEC          : Z := 0x1490a.   (* [comment removed for export] *)
Definition L_STR_WAIT_USEC          : Z := 0x1480f.   (* [comment removed for export] *)
Definition L_EXECUTION_CONTEXT_PROP : Z := 0x15859.   (* [comment removed for export] *)
Definition L_TYPEID_CONFIG          : Z := 0x7e7e8.   (* [comment removed for export] *)
Definition L_TYPEID_SCHED           : Z := 0x7ed70.   (* [comment removed for export] *)

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
Definition ErrCode (m : mem) (a : Z) (E : ecv) : Prop := rw_cells usegs m a (ErrCodeCells E) /\ ec_ok E.

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
  rw_cells usegs m a (FlatBufCells F) /\ fb_ok LB F /\ zlength ds = fb_size F
  /\ (F <> FB_empty -> exists pre junk,
        rw_cells usegs m (fb_begin F) [CB (Z.to_nat (fb_in F - fb_begin F)) pre; CB (length ds) ds;
                                     CB (Z.to_nat (fb_end F - fb_out F)) junk]).

(* [comment removed for export] *)
Definition PMutexCells (lk : Z) : list cell := [CB 4 (zeros 4); C4 (wz lk); CB 32 (zeros 32)].
Definition PMutex (m : mem) (a : Z) (lk : Z) : Prop := rw_cells usegs m a (PMutexCells lk) /\ (lk = 0 \/ lk = EBUSY) /\ a mod 4 = 0.
(* [comment removed for export] *)
Definition PMutexZeroCells : list cell := [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
Definition PCondCells (clk : Z) : list cell := [CB 16 (zeros 16); C4 (wz clk); CB 12 (zeros 12); C4 (wz 0); CB 4 (zeros 4); C8 (wz 0)].
Definition PCond (m : mem) (a : Z) (clk : Z) : Prop := rw_cells usegs m a (PCondCells clk) /\ (clk = 0 \/ clk = CLOCK_MONOTONIC) /\ a mod 8 = 0.

(* [comment removed for export] *)
Record svch := mkSVC { sv_vptr : Z ; sv_ti : Z ; sv_id : Z ; sv_owner : Z ; sv_next : Z ; sv_destroy : Z }.
Definition SvcHdrCells (S : svch) : list cell :=
  [C8 (wz (sv_vptr S)); C8 (wz (sv_ti S)); C8 (wz (sv_id S)); C8 (wz (sv_owner S)); C8 (wz (sv_next S)); C8 (wz (sv_destroy S))].

(* [comment removed for export] *)
Definition CookieCells (junk7 : list byte) : list cell := [CB 8 (zeros 8); CB 7 junk7].

(* [comment removed for export] *)
Definition AllocImpl (LB : list block) (m : mem) (a : Z) : Prop :=
  exists p junk, In (p, a, SZ_ALLOCIMPL) LB /\ rw_cells usegs m a [C8 (wz VP_ALLOCIMPL); CB 8 junk].

(* [comment removed for export] *)
Definition Registry (LB : list block) (m : mem) (r : Z) (owner first lk : Z) : Prop :=
  exists p j0 j7, In (p, r, NEWSZ_REG) LB
  /\ rw_cells usegs m r [CB 8 j0]
  /\ PMutex m (r + O_REG_MUTEX) lk
  /\ rw_cells usegs m (r + O_REG_OWNER) [C8 (wz owner); C8 (wz first)]
  /\ rw_cells usegs m (r + SZ_REG) (CookieCells j7).

(* [comment removed for export] *)
Definition ConfigSvc (LB : list block) (m : mem) (c : Z) (S : svch) : Prop :=
  exists p j4 j7, In (p, c, NEWSZ_CFG) LB
  /\ rw_cells usegs m c (SvcHdrCells S ++ [C4 (wz (2^32 - 1)); CB 4 j4] ++ CookieCells j7)
  /\ sv_vptr S = VP_CONFIG_SVC /\ sv_destroy S = P_DESTROY_ALLOC_CONFIG.

(* [comment removed for export] *)
Record schv := mkSCH { sch_hdr : svch ; sch_lk : Z ; sch_stopped : Z ; sch_shutdown : Z }.
Definition Scheduler (LB : list block) (m : mem) (s : Z) (S : schv) : Prop :=
  exists p j50 jm j109 je jt j219 j7, In (p, s, NEWSZ_SCH) LB
  /\ rw_cells usegs m s (SvcHdrCells (sch_hdr S))
  /\ rw_cells usegs m (s + O_SCH_ONE_THREAD) [CB 2 [b8 0; b8 0]; CB 6 j50]           (* [comment removed for export] *)
  /\ rw_cells usegs m (s + O_SCH_MUTEX) [CB 8 jm]                                     (* [comment removed for export] *)
  /\ PMutex m (s + O_SCH_PMUTEX) (sch_lk S)                                            (* [comment removed for export] *)
  /\ rw_cells usegs m (s + O_SCH_SPIN) [C4 (wz 0); CB 1 [b8 1]; CB 3 j109]            (* [comment removed for export] *)
  /\ rw_cells usegs m (s + O_SCH_EVENT) [CB 8 je]                                     (* [comment removed for export] *)
  /\ PCond m (s + O_SCH_COND) CLOCK_MONOTONIC                                          (* [comment removed for export] *)
  /\ rw_cells usegs m (s + O_SCH_EVSTATE)
       [C8 (wz 0);                                   (* [comment removed for export] *)
        C8 (wz 0); C8 (wz P_SCHED_GET_DEFAULT_TASK); (* [comment removed for export] *)
        C8 (wz 0); C8 (wz 0); C4 (wz 0); CB 4 jt;    (* [comment removed for export] *)
        CB 3 [b8 1; b8 (sch_stopped S); b8 (sch_shutdown S)]; CB 5 j219;   (* [comment removed for export] *)
        C8 (wz 0);                                   (* [comment removed for export] *)
        C8 (wz 0); C8 (wz 0);                        (* [comment removed for export] *)
        C8 (wz u64max); C8 (wz u64max);              (* [comment removed for export] *)
        C8 (wz 0)]                                   (* [comment removed for export] *)
  /\ rw_cells usegs m (s + SZ_SCH) (CookieCells j7)
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
  /\ rw_cells usegs m b (SpcHdrCells (im_hdr I) j7) /\ spc_ok (im_hdr I) /\ spc_vptr (im_hdr I) = VP_SPCI_IMPL
  /\ PMutex m (b + O_SPC_STORAGE + O_IMPL_MUTEX) (im_lk I)
  /\ rw_cells usegs m (b + O_SPC_STORAGE + O_IMPL_VEC_BEGIN)
       [C8 (wz (im_vb I)); C8 (wz (im_vb I + 8 * zlength (im_states I))); C8 (wz (im_vb I + 8 * im_vcap I))]
  /\ zlength (im_states I) <= im_vcap I
  /\ ((im_vcap I = 0 /\ im_vb I = 0)
      \/ (exists q junk, In (q, im_vb I, 8 * im_vcap I) LB /\ rblock_range (im_vb I) (8 * im_vcap I) /\ 0 < im_vcap I
           /\ rw_cells usegs m (im_vb I) [CB (8 * length (im_states I)) (flat_map le8z (im_states I));
                                         CB (Z.to_nat (8 * (im_vcap I - zlength (im_states I)))) junk])).

(* [comment removed for export] *)
Definition AnyExecCells (a ioc : Z) (j16 : list byte) : list cell :=
  [C8 (wz ioc); CB 16 j16; C8 (wz T_ANYEX_OBJECT_FNS); C8 (wz a); C8 (wz T_ANYEX_TARGET_FNS); C8 (wz T_ANYEX_PROP_FNS)].

(* [comment removed for export] *)
Record statev := mkST { st_hdr : spcv ; st_lk : Z ; st_fb : fbv ; st_code : Z ; st_nread : Z ; st_nread_bytes : Z }.
Definition StateBlock (LB : list block) (m : mem) (b ioc implb : Z) (S : statev) (ds : list byte) : Prop :=
  exists p j7 j16 j4, In (p, b, SZ_SPCI_STATE) LB /\ rblock_range b SZ_SPCI_STATE
  /\ rw_cells usegs m b (SpcHdrCells (st_hdr S) j7) /\ spc_ok (st_hdr S) /\ spc_vptr (st_hdr S) = VP_SPCI_STATE
  /\ rw_cells usegs m (b + 32 + O_ST_EXEC) (AnyExecCells (b + 32 + O_ST_EXEC) ioc j16)
  /\ rw_cells usegs m (b + 32 + O_ST_WP_PX) [C8 (wz (implb + O_SPC_STORAGE)); C8 (wz implb)]
  /\ PMutex m (b + 32 + O_ST_MUTEX) (st_lk S)
  /\ FlatBuf LB m (b + 32 + O_ST_FB) (st_fb S) ds
  /\ PCond m (b + 32 + O_ST_CV) 0
  /\ rw_cells usegs m (b + 32 + O_ST_OP)
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
  /\ rw_cells usegs m v (SvcHdrCells S ++ [C8 (wz (implb + O_SPC_STORAGE)); C8 (wz implb)] ++ CookieCells j7)
  /\ sv_vptr S = VP_SSVC /\ sv_destroy S = P_DESTROY_ALLOC_SSVC.

(* [comment removed for export] *)
Definition BasicStreamCells (stateb : Z) : list cell :=
  [C8 (wz (stateb + O_SPC_STORAGE)); C8 (wz stateb); C8 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
Definition IoCtxCells (allocb regb schedb : Z) : list cell := [C8 (wz allocb); C8 (wz regb); C8 (wz schedb)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IoWorld2 (LB : list block) (m : mem) (ioc allocb regb cfgb schedb : Z) : Prop :=
  rw_cells usegs m ioc (IoCtxCells allocb regb schedb)
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
  rw_cells usegs m ioc (IoCtxCells allocb regb schedb)
  /\ rw_cells usegs m bs (BasicStreamCells stateb)
  /\ AllocImpl LB m allocb
  /\ Registry LB m regb ioc ssvcb 0
  /\ ConfigSvc LB m cfgb (mkSVC VP_CONFIG_SVC L_TYPEID_CONFIG 0 ioc 0 P_DESTROY_ALLOC_CONFIG)
  /\ Scheduler LB m schedb (mkSCH (mkSVC VP_SCHED L_TYPEID_SCHED 0 ioc cfgb P_DESTROY_ALLOC_SCHED) 0 0 0)
  /\ StreamSvc LB m ssvcb (mkSVC VP_SSVC 0 G_ID_SSVC ioc schedb P_DESTROY_ALLOC_SSVC) implb
  /\ ImplBlockV LB m implb 1 2 [stateb + O_SPC_STORAGE] 1
  /\ StateBlock LB m stateb ioc implb (mkST (mkSPC VP_SPCI_STATE 1 1 1) 0 F code nread nread_bytes) ds.
(* [comment removed for export] *)
Definition IoWorld4 (LB : list block) (m : mem) (ioc allocb regb cfgb schedb ssvcb implb : Z) : Prop :=
  rw_cells usegs m ioc (IoCtxCells allocb regb schedb)
  /\ AllocImpl LB m allocb
  /\ Registry LB m regb ioc ssvcb 0
  /\ ConfigSvc LB m cfgb (mkSVC VP_CONFIG_SVC L_TYPEID_CONFIG 0 ioc 0 P_DESTROY_ALLOC_CONFIG)
  /\ Scheduler LB m schedb (mkSCH (mkSVC VP_SCHED L_TYPEID_SCHED 0 ioc cfgb P_DESTROY_ALLOC_SCHED) 0 0 0)
  /\ StreamSvc LB m ssvcb (mkSVC VP_SSVC 0 G_ID_SSVC ioc schedb P_DESTROY_ALLOC_SSVC) implb
  /\ ImplBlockV LB m implb 1 1 [] 1.

(* [comment removed for export] *)
Lemma ErrCode_clear_intro : forall m a, rw_cells usegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> ErrCode m a EC_clear.
Proof. intros m a H. split; [exact H|]. unfold ec_ok, EC_clear; cbn; lia. Qed.
Lemma FlatBuf_empty_intro : forall LB m a,
  rw_cells usegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz u64max)] -> FlatBuf LB m a FB_empty [].
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
     rw_cells usegs m VP_ALLOCIMPL   (wcells [VS_ALLOCIMPL_0; VS_ALLOCIMPL_8; VS_ALLOCIMPL_16; VS_ALLOCIMPL_24; VS_ALLOCIMPL_32])
  /\ rw_cells usegs m VP_CONFIG_SVC  (wcells [VS_CONFIG_SVC_0; VS_CONFIG_SVC_8; VS_CONFIG_SVC_16; VS_CONFIG_SVC_24; VS_CONFIG_SVC_32])
  /\ rw_cells usegs m VP_SCHED       (wcells [VS_SCHED_0; VS_SCHED_8; VS_SCHED_16; VS_SCHED_24])
  /\ rw_cells usegs m VP_SSVC        (wcells [VS_SSVC_0; VS_SSVC_8; VS_SSVC_16; VS_SSVC_24])
  /\ rw_cells usegs m VP_SPCI_IMPL   (wcells [VS_SPCI_IMPL_0; VS_SPCI_IMPL_8; VS_SPCI_IMPL_16; VS_SPCI_IMPL_24; VS_SPCI_IMPL_32; VS_SPCI_IMPL_40; VS_SPCI_IMPL_48])
  /\ rw_cells usegs m VP_SPCI_STATE  (wcells [VS_SPCI_STATE_0; VS_SPCI_STATE_8; VS_SPCI_STATE_16; VS_SPCI_STATE_24; VS_SPCI_STATE_32; VS_SPCI_STATE_40; VS_SPCI_STATE_48])
  /\ rw_cells usegs m VP_PARSER      (wcells [VS_PARSER_0; VS_PARSER_8; VS_PARSER_16; VS_PARSER_24; VS_PARSER_32; VS_PARSER_40; VS_PARSER_48; VS_PARSER_56; VS_PARSER_64; VS_PARSER_72; VS_PARSER_80; VS_PARSER_88])
  /\ rw_cells usegs m VP_HTTP_ECAT   (wcells [VS_HTTP_ECAT_0; VS_HTTP_ECAT_8; VS_HTTP_ECAT_16; VS_HTTP_ECAT_24; VS_HTTP_ECAT_32; VS_HTTP_ECAT_40; VS_HTTP_ECAT_48])
  /\ rw_cells usegs m T_ANYEX_OBJECT_FNS (wcells T_ANYEX_OBJECT_FNS_words)
  /\ rw_cells usegs m T_ANYEX_TARGET_FNS (wcells T_ANYEX_TARGET_FNS_words)
  /\ rw_cells usegs m T_ANYEX_PROP_FNS   (wcells T_ANYEX_PROP_FNS_words)
  /\ rw_cells usegs m T_ANYEX_PROP_FNS_VOID (wcells T_ANYEX_PROP_FNS_VOID_words)
  /\ rw_cells usegs m (L_TYPEID_CONFIG + 8) (wcells [TI_NAME_CONFIG])
  /\ rw_cells usegs m (L_TYPEID_SCHED + 8)  (wcells [TI_NAME_SCHED])
  /\ rw_cells usegs m G_SYSTEM_CAT_INST (wcells [W_SYSTEM_CAT_VPTR; W_SYSTEM_CAT_ID])
  /\ rw_cells usegs m G_MISC_CAT_INST   (wcells [W_MISC_CAT_VPTR; W_MISC_CAT_ID]).

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
  XStatics m -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv : Z * Z => (0x80088 <= fst iv \/ snd iv <= 0x7e4b8) /\ (0x84c50 <= fst iv \/ snd iv <= 0x84b98)) W ->
  XStatics m'.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMalloc_iface_stmt.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.XS.XStatics); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.USegs.usegs); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.I); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.Lists.List.Forall_inv); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.Lists.List.Forall_inv_tail); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VP_ALLOCIMPL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.XS.wcells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_ALLOCIMPL_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_ALLOCIMPL_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_ALLOCIMPL_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_ALLOCIMPL_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_ALLOCIMPL_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VP_CONFIG_SVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_CONFIG_SVC_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_CONFIG_SVC_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_CONFIG_SVC_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_CONFIG_SVC_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_CONFIG_SVC_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VP_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SCHED_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SCHED_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SCHED_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SCHED_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VP_SSVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SSVC_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SSVC_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SSVC_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SSVC_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VP_SPCI_IMPL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_IMPL_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_IMPL_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_IMPL_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_IMPL_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_IMPL_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_IMPL_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_IMPL_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VP_SPCI_STATE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_STATE_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_STATE_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_STATE_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_STATE_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_STATE_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_STATE_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_SPCI_STATE_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VP_PARSER); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_56); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_72); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_80); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_PARSER_88); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VP_HTTP_ECAT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_HTTP_ECAT_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_HTTP_ECAT_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_HTTP_ECAT_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_HTTP_ECAT_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_HTTP_ECAT_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_HTTP_ECAT_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.VS_HTTP_ECAT_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.T_ANYEX_OBJECT_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.T_ANYEX_OBJECT_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.T_ANYEX_TARGET_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.T_ANYEX_TARGET_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.T_ANYEX_PROP_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.T_ANYEX_PROP_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.T_ANYEX_PROP_FNS_VOID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.T_ANYEX_PROP_FNS_VOID_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.L_TYPEID_CONFIG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.TI_NAME_CONFIG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.L_TYPEID_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.TI_NAME_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.G_SYSTEM_CAT_INST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.W_SYSTEM_CAT_VPTR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.W_SYSTEM_CAT_ID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.G_MISC_CAT_INST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.W_MISC_CAT_VPTR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.W_MISC_CAT_ID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.or_morph); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@kc__1 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))|] [|@iv; @FW; @W; @l; @p; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__arith; @H1; @IH; @hi; @lo; @z; @a; @HA; @n; @A; @x; @y; @m; @H14; @H13; @H12; @H11; @H10; @H9; @H8; @H7; @H6; @H5; @H4; @H3; @H2; @H0; @H; @D; @WM; @MU; @XS; @m'|] "#DB#g%R#u#x$<$=$;$C$E#{##%@%C%:%8%6%4%,${#$$s$$#a#d#g$k$f$a$[$T#-#)#,#.#b#%#*#1#5#9#=#A#E#I#M#Q#U#Y#]#f#e#0%G#&#4#2#8#6#<#:#@$.#>#D#B#H#k#(#F#L%S#'#J#P#N#T#R#X$4#V#\#p#Z#j#n#m#r#+$3$6$5$9$K$L#/#^#_#`#q#s#t#w#~$#$($,$7$8$:$F$H$N$M$O$P$I$Q$)$%$Z$Y$X$W$V$`$_$^$]$\$e$d$c$b$j$i$h$g$r$q$p$o$n$m$l$z$y$x$w$v$u$t%+%*%)%(%'%&%%%$%#$~$}$|%3%2%1%0%/%.%-%5%7%9%;%<%=%>%?%B%A%E%D#3#7#;#?#C#G#K#O#S#W#[#c%N%P%Q#l#y$S$2#o$A$@#z#}$*$J$>%L%M%K#|$B$?$G$-$U%H%O%J%I%F$R$&%R$1$0#v$/$D$'$+J%/%%0'#*%%1$%2$%3'%4*%5%#6%%6$%7&%8%%9*%:&%;/%<)%=$%>%#U$%?*%@&%A'%B$%C$%D5%E)%F'$%&%G-%H(%I&%J/%K%%L&%M&%N%%O%%P$%Q'USdSS'Sb'#'#'#'#'#USe#USf#USe(USf#USs#k##&#USgS$WStSFS4S$WSuCSFS4VSvDD'-'#'#,#'#'#'#,#,#'#'#'#'#3#WSwDDK'Sb'#'#'#'#'#'#'#'#'#'#,#'#'#'#,#'#'#'#3#,Sb,#,#,#,#'#'#,#'#'#,#'#,#,#,#'#'#'#3#,s#&'#'#,#,#'#'#'#,#'#,#'#'#'#'#3#'/,#,#,#'#'#,#,#'#'#'#3#,s#,'#,#'#'#,#,#,#,#'#'#'#3#,s#7,#'#'#'#,#,#'#'#'#3#,:,#'#'#,#'#,#'#'#'#'#3#,s#Q,#'#,#,#,#,#'#'#,#'#'#'#3#,/'#'#'#'#,#'#,#'#'#'#3#,,'#'#,#,#'#'#'#3#,s#0'#'#,#,#,#'#'#'#3#'s#/'#'#'#'#,#,#'#,#'#'#'#3#,s#.'#'#,#'#'#,#'#'#'#3#,s#8,#'#'#,#'#'#'#'#3#,4'#,#'#'#'#3#,s#>,#'#,#'#'#'#3#,s#v,#,#'#,#'#'#'#3#'s#u,#'#,#,#,#'#'#'#'#3#'s$O'#'#'#'#3#%s$rs%*WSxDDK,Sb,#,#,#,#'#'#,#,#'#'#,#,#'#'#'#'#'#3#%6s$t*8#,s%\'#'#,#,#'#,#,#,#,#,#,#'#'#'#3#%s$vs%Q'-,#'#'#'#'#'#'#3#%s#2s$t*-##?#j#$s%m#Es%n#ST%s%9S$+S$K%#s%N#%#%s$}S$%&s%.#$#*&#Es%w,KAS$SXSFk#%$#j#&s&.#HSSEs%|1#j#%#SyAS$S0STk#%*#-SSS4S$Es&%6#-SSSFS4A#S5S0k#%%#k##(#k#'s&:#j#(s&+#AS$S1Shk#%4#IDDSFS4-SS#S$Es&0A#IDDSXSFYSzs&2s###S4KUs#$$+S2S/%#ST%SXS2*$#ASFS2S/&Si&#&#&#&#CD#CD&CDSiDD$#DD&#F#S_CD*CD-CD/DD$#DD&#F#S_DD.%F#S_DD*-F#S_HSN-SN.#-SN/#-SN&#-SN)#-SN,#-SN-#-SN4#-SN5#USdSNVSjDSXUS{DXSkD$S4#VSjDSFXSkD$S$#US|DUS}D4Ds&<GDs$'(D$H#)&GEEF#IGDs&q4Ds&.(D$H#)*GEEF#I6+GEEF'#4Ds%~(D#H+).GEEF#I4Ds%u(D+H#)1GEEF#I62GEEF&#/3GEEF*#US~EGDSb(D0H#)7GEEF#IGDs''7D&#(D#H9);GEEF#I/<GEEF'#(D0H*)>GEEF#I(D(H5)@GEEF#I/AGEEF%#6BGEEF(#(D,HA)s#$GEEF#I(D@H2)s#&GEEF#I6s#'GEEF%#\Sls#(GEEF(6#\Sls#)GEEF87#VT#s#*F.SmSnVT$KS4WT%Sm#Snm$%#WT&DT'S$XT(KS4$#l#)*)#l#*s#4s#3#l#+s#;s#:#j#,D#j#-D#j#.D#j#/D#%s&qS4%SFs&_*$#%s&QS4%SFs&F*$##&#+S$S4%#s&y#s$0#%%s&X#s$.#*%#+S4SF%#SX%STS4*$#k##'#k##.#k#,D#k#-D#k#.D#k#/D#ZKSTS0S2SoS$S/l#0;$#IDDSTSXYT)s'Rs$C#SFS$US4#8s#{s#z&#-SS&SFA#S2S/m#%#l#1s$(s$'#j#%s$+#j#2s$/#j#&s'k#j#3D#j#4D#V#S$Kj#5D#j#5D#YT*DDs$8#Kj#6SS#ZT+SSs$Gs$D#S1SFj#7s$L#j#8D#j#9D#AS1S4S$k##s$P#k#8D#k#9D#HD-DT,#-DT-#-DT.#-DT/#-DT0#9#$CS0S.#-DT1*-DT2#-DT3#-DT4#-DT5#9#$CS0S-#-DT61-DT7#-DT8#-DT9#9#$CS0S,#-DT:7-DT;#-DT<#-DT=#9#$CS0S+#-DT>=-DT?#-DT@#-DTA#-DTB#-DTC#-DTD#9#$CS0S*#-DTEs#&-DTF#-DTG#-DTH#-DTI#-DTJ#-DTK#9#$CS0S%#-DTLs#/-DTM#-DTN#-DTO#-DTP#-DTQ#-DTR#-DTS#-DTT#-DTU#-DTV#-DTW#9#$CS0S##-DTXs#=-DTY#-DTZ#-DT[#-DT\#-DT]#-DT^#9#$CS0R#9T_$CS0Q#9T`$CS0P#9Ta$CS0O#9Tb$CS0N#3s(h+Tc#-DTds#P9#$CS0%#+Te'-DTfs#T9#$CS0%#-DTgs#W-DTh#9#$CS0L#-DTis#[-DTj#9#$CS0M##'##,##1##7##:##=##@##s####s#-##s#<##s#F##s#P##s#W##s#^##s#f#j####$CS5S-s#b$CS5S,s#]$CS5S+s#X$CS5S*s#P$CS5S%s#H$CS5S#s#;$CS5Rs#3$CS5Qs#2$CS5Ps#1$CS5Os#0$CS5Ns#/$CS5s#-s#+$CS5s#*s#($CS5Ls#%$CS5MB#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CShS.s$*$CS1S-s$$$CS1S,s#{$CS1S+s#v$CS1S*s#n$CS1S%s#f$CS1S#s#Y$CS1Rs#Q$CS1Qs#P$CS1Ps#O$CS1Os#N$CS1Ns#M$CS1s#Ks#I$CS1s#Hs#F$CS1Ls#C$CS1Ms#@#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CS/S-s$A$CS/S,s$<$CS/S+s$7$CS/S*s$/$CS/S%s$'$CS/S#s#v$CS/Rs#n$CS/Qs#m$CS/Ps#l$CS/Os#k$CS/Ns#j$CS/s#hs#f$CS/s#es#c$CS/Ls#`$CS/Ms#]#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CS/S.s$e##$j##%#$CS2S,s$[$CS2S+s$V$CS2S*s$N$CS2S%s$F$CS2S#s$9$CS2Rs$1$CS2Qs$0$CS2Ps$/$CS2Os$.$CS2Ns$-$CS2s$+s$)$CS2s$(s$&$CS2Ls$#$CS2Ms#|#$##&##(##*##,##.##0##2##4##6##8##:##<#$CSoS-s$|$CSDS,s$w$CSDS+s$r$CSDS*s$j$CSDS%s$b$CSDS#s$U$CSDRs$M$CSDQs$L$CSDPs$K$CSDOs$J$CSDNs$I$CSDs$Gs$E$CSDs$Ds$B$CSDLs$?$CSDMs$<#$##&##(##*##,##.##0##2##4##6##8##:##<#$CS6S,s%6$CS6S+s%1$CS6S*s%)$CS6S%s$}$CS6S#s$p$CS6Rs$h$CS6Qs$g$CS6Ps$f$CS6Os$e$CS6Ns$d$CS6s$bs$`$CS6s$_s$]$CS6Ls$Z$CS6Ms$W#$##&##(##*##,##.##0##2##4##6##8##:##<#$CS6S.s%^$CS6S-s%X##%#%#j##'#$CSHS+s%P$CSHS*s%H$CSHS%s%@$CSHS#s%3$CSHRs%+$CSHQs%*$CSHPs%)$CSHOs%($CSHNs%'$CSHs%%s%#$CSHs$~s$|$CSHLs$y$CSHMs$v#$##&##(##*##,##.##0##2##4##6##8##:#$CTkS,s%o$CSGS+s%j$CSGS*s%b$CSGS%s%Z$CSGS#s%M$CSGRs%E$CSGQs%D$CSGPs%C$CSGOs%B$CSGNs%A$CSGs%?s%=$CSGs%<s%:$CSGLs%7$CSGMs%4#$##&##(##*##,##.##0##2##4##6##8##:#$CS7S+s&'$CS7S*s%{$CS7S%s%s$CS7S#s%f$CS7Rs%^$CS7Qs%]$CS7Ps%\$CS7Os%[$CS7Ns%Z$CS7s%Xs%V$CS7s%Us%S$CS7Ls%P$CS7Ms%M#$##&##(##*##,##.##0##2##4##6##8##:#$CS7S.s&S$CS7S-s&M$CS7S,s&H##&#%##'#j##)#$CSJS*s&>$CSJS%s&6$CSJS#s&)$CSJRs%}$CSJQs%|$CSJPs%{$CSJOs%z$CSJNs%y$CSJs%ws%u$CSJs%ts%r$CSJLs%o$CSJMs%l#$##&##(##*##,##.##0##2##4##6##8#$CTlS+s&^$CSIS*s&V$CSIS%s&N$CSIS#s&A$CSIRs&9$CSIQs&8$CSIPs&7$CSIOs&6$CSINs&5$CSIs&3s&1$CSIs&0s&.$CSILs&+$CSIMs&(#$##&##(##*##,##.##0##2##4##6##8#$CS8S*s&m$CS8S%s&e$CS8S#s&X$CS8Rs&P$CS8Qs&O$CS8Ps&N$CS8Os&M$CS8Ns&L$CS8s&Js&H$CS8s&Gs&E$CS8Ls&B$CS8Ms&?#$##&##(##*##,##.##0##2##4##6##8#$CS8S.s'D$CS8S-s'>$CS8S,s'9$CS8S+s'4##'#%##'##)#j##+#$CSLS%s'($CSLS#s&w$CSLRs&o$CSLQs&n$CSLPs&m$CSLOs&l$CSLNs&k$CSLs&is&g$CSLs&fs&d$CSLLs&a$CSLMs&^#$##&##(##*##,##.##0##2##4##6#$CTmS*s'F$CSKS%s'>$CSKS#s'1$CSKRs')$CSKQs'($CSKPs''$CSKOs'&$CSKNs'%$CSKs'#s&}$CSKs&|s&z$CSKLs&w$CSKMs&t#$##&##(##*##,##.##0##2##4##6#$CS9S%s'S$CS9S#s'F$CS9Rs'>$CS9Qs'=$CS9Ps'<$CS9Os';$CS9Ns':$CS9s'8s'6$CS9s'5s'3$CS9Ls'0$CS9Ms'-#$##&##(##*##,##.##0##2##4##6#$CS9S.s(1$CS9S-s(+$CS9S,s(&$CS9S+s'}$CS9S*s'u##(#%##'##)##+#j##-#$CSOS#s'e$CSORs']$CSOQs'\$CSOPs'[$CSOOs'Z$CSONs'Y$CSOs'Ws'U$CSOs'Ts'R$CSOLs'O$CSOMs'L#$##&##(##*##,##.##0##2##4#$CTnS%s(*$CSMS#s'y$CSMRs'q$CSMQs'p$CSMPs'o$CSMOs'n$CSMNs'm$CSMs'ks'i$CSMs'hs'f$CSMLs'c$CSMMs'`#$##&##(##*##,##.##0##2##4#$CS:S#s(0$CS:Rs(($CS:Qs('$CS:Ps(&$CS:Os(%$CS:Ns($$CS:s'~s'|$CS:s'{s'y$CS:Ls'v$CS:Ms's#$##&##(##*##,##.##0##2##4#$CS:S.s(v$CS:S-s(p$CS:S,s(k$CS:S+s(f$CS:S*s(^$CS:S%s(V##)#%##'##)##+##-#j##/#$CSQRs(G$CSQQs(F$CSQPs(E$CSQOs(D$CSQNs(C$CSQs(As(?$CSQs(>s(<$CSQLs(9$CSQMs(6#$##&##(##*##,##.##0##2#$CToS#s(a$CSPRs(Y$CSPQs(X$CSPPs(W$CSPOs(V$CSPNs(U$CSPs(Ss(Q$CSPs(Ps(N$CSPLs(K$CSPMs(H#$##&##(##*##,##.##0##2#$CS;Rs(j$CS;Qs(i$CS;Ps(h$CS;Os(g$CS;Ns(f$CS;s(ds(b$CS;s(as(_$CS;Ls(\$CS;Ms(Y#$##&##(##*##,##.##0##2#$CS;S.s)[$CS;S-s)U$CS;S,s)P$CS;S+s)K$CS;S*s)C$CS;S%s);$CS;S#s).##*#%##'##)##+##-##/#j##1#$CSUQs),$CSUPs)+$CSUOs)*$CSUNs))$CSUs)'s)%$CSUs)$s(~$CSULs({$CSUMs(x#$##&##(##*##,##.##0#$CTpRs)=$CSRQs)<$CSRPs);$CSROs):$CSRNs)9$CSRs)7s)5$CSRs)4s)2$CSRLs)/$CSRMs),#$##&##(##*##,##.##0#$CS<Qs)K$CS<Ps)J$CS<Os)I$CS<Ns)H$CS<s)Fs)D$CS<s)Cs)A$CS<Ls)>$CS<Ms);#$##&##(##*##,##.##0#$CS<S.s*<$CS<S-s*6$CS<S,s*1$CS<S+s*,$CS<S*s*$$CS<S%s)x$CS<S#s)k$CS<Rs)c##+#%##'##)##+##-##/##1#j##3#$CSYPs)i$CSYOs)h$CSYNs)g$CSYs)es)c$CSYs)bs)`$CSYLs)]$CSYMs)Z#$##&##(##*##,##.#$CTqQs)x$CSVPs)w$CSVOs)v$CSVNs)u$CSVs)ss)q$CSVs)ps)n$CSVLs)k$CSVMs)h#$##&##(##*##,##.#$CS=Ps*($CS=Os*'$CS=Ns*&$CS=s*$s)~$CS=s)}s){$CS=Ls)x$CS=Ms)u#$##&##(##*##,##.#$CS=S.s*u$CS=S-s*o$CS=S,s*j$CS=S+s*e$CS=S*s*]$CS=S%s*U$CS=S#s*H$CS=Rs*@$CS=Qs*?##,#%##'##)##+##-##/##1##3#j##5#$CS[Os*F$CS[Ns*E$CS[s*Cs*A$CS[s*@s*>$CS[Ls*;$CS[Ms*8#$##&##(##*##,#$CTrPs*S$CSZOs*R$CSZNs*Q$CSZs*Os*M$CSZs*Ls*J$CSZLs*G$CSZMs*D#$##&##(##*##,#$CS>Os*]$CS>Ns*\$CS>s*Zs*X$CS>s*Ws*U$CS>Ls*R$CS>Ms*O#$##&##(##*##,#$CS>S.s+N$CS>S-s+H$CS>S,s+C$CS>S+s+>$CS>S*s+6$CS>S%s+.$CS>S#s*}$CS>Rs*u$CS>Qs*t$CS>Ps*s##-#%##'##)##+##-##/##1##3##5#j##7#$CS]Ns*{$CS]s*ys*w$CS]s*vs*t$CS]Ls*q$CS]Ms*n#$##&##(##*#$CTsOs+*$CS\Ns+)$CS\s+'s+%$CS\s+$s*~$CS\Ls*{$CS\Ms*x#$##&##(##*#$CS?Ns+2$CS?s+0s+.$CS?s+-s++$CS?Ls+($CS?Ms+%#$##&##(##*#$CS?S.s,#$CS?S-s+y$CS?S,s+t$CS?S+s+o$CS?S*s+g$CS?S%s+_$CS?S#s+R$CS?Rs+J$CS?Qs+I$CS?Ps+H$CS?Os+G##.#%##'##)##+##-##/##1##3##5##7#j##9#$CS`s+Os+M$CS`s+Ls+J$CS`Ls+G$CS`Ms+D#$##&##(#$CTtNs+Y$CS^s+Ws+U$CS^s+Ts+R$CS^Ls+O$CS^Ms+L#$##&##(#$CS@s+^s+\$CS@s+[s+Y$CS@Ls+V$CS@Ms+S#$##&##(#$CS@S.s,P$CS@S-s,J$CS@S,s,E$CS@S+s,@$CS@S*s,8$CS@S%s,0$CS@S#s,#$CS@Rs+w$CS@Qs+v$CS@Ps+u$CS@Os+t$CS@Ns+s##/#%##'##)##+##-##/##1##3##5##7##9#j##;#$CScs+zs+x$CScLs+u$CScMs+r#$##&#$CTus,'s,%$CSas,$s+~$CSaLs+{$CSaMs+x#$##&#$CSAs,)s,'$CSALs,$$CSAMs+}#$##&#$CSAS.s,y$CSAS-s,s$CSAS,s,n$CSAS+s,i$CSAS*s,a$CSAS%s,Y$CSAS#s,L$CSARs,D$CSAQs,C$CSAPs,B$CSAOs,A$CSANs,@$CSAs,>s,<##0#%##'##)##+##-##/##1##3##5##7##9##;#j##=#$CSpLs,C$CSpMs,@#$#$CSqs,Ls,J$CSrLs,G$CSrMs,D#$#$CS'Ls,J$CS'Ms,G#$#$CS'S.s-B$CS'S-s-<$CS'S,s-7$CS'S+s-2$CS'S*s-*$CS'S%s,~$CS'S#s,q$CS'Rs,i$CS'Qs,h$CS'Ps,g$CS'Os,f$CS'Ns,e$CS's,cs,a$CS's,`s,^##1#%##'##)##+##-##/##1##3##5##7##9##;##=#j##?#$CS3Ms,f$CTvLs,k$CS(Ms,h$CS(S.s-b$CS(S-s-\$CS(S,s-W$CS(S+s-R$CS(S*s-J$CS(S%s-B$CS(S#s-5$CS(Rs--$CS(Qs-,$CS(Ps-+$CS(Os-*$CS(Ns-)$CS(s-'s-%$CS(s-$s,~$CS(Ls,{##2#%##'##)##+##-##/##1##3##5##7##9##;##=#:s.#5#,s0V,#'#'#'#'#,#'#'#'#'#'#3#%s2ks2B&s/g&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#5#+s2g#%#s3H#s#)#%s2ws2j%&s3(#$#*&#,s4$'#'#'#3#+s2s#%#s3T#s#5#%%s33#/#*%#.S)s#90s#:s#:#j#:DK%S$KUTw#j#;D#j#:D#XTxDDTys0q.D#j#<D#j#8D#.Ds3(5K.D#j#:SW#.D8BSWDDDSESE00$s#&9#;DDDDDDS&111S&)s3.s3.(s#&:#.Ds3k1DDJ3J/s#';$s3ls3l#2s#Ms#'s#M;5#.S)s#&0s#'s#'#.Ds3M1DDJ8J4s#,@)s3Ns3N#2s#*s#)s#*>%#<s#,s#)@>(#4Ds38(Ds06H#)s0=GEEF#I4Ds#'7D&#(D#Hs0?)s0AGEEF#I/s0BGEEF'#(Ds06H*)s0DGEEF#I(D(Hs0;)s0FGEEF#I/s0GGEEF%#6s0HGEEF(#l#)#s/}s/wl#*s0Os0K#l#+s0[s0R#l#0#s#/K=s#;s#05#m##s#<%s3uS.+S.s#E%#s4.#%#%s3]S.%&s3j#$#*&#m#+#+S.s$#%#s46#-#%%s3q#+#*%#m#)#>S.s$*#?CSBSCS(S.s/MSaS3S'#:s/G5#'s$-'#'#,#,#'#'#'#'#'#'#3#%s49s3a+s3bs#e%#s4N#%#%s3}s3e%&s4.#$#*&#+s3is#`%#s4U#,#%%s44#*#*%#.S)0011#.Ds3q;DDDDDDS&s#`s#`s#`S&s#Xs3rs3r#s#us#is#R1DDJs#aJs#]3,#s4^s4^s#Q2535,&#.S)2033#1DDJs#eJs#a70's4?s4?s#P2545.$#<740.'#4Ds3z(Ds1'H#)s1.GEEF#I7D%s#O(D#Hs1/)s11GEEF#I/s12GEEF&#(Ds1&H))s14GEEF#I(D(Hs1+)s16GEEF#I/s17GEEF%#6s18GEEF(#l#)#s0ms0gl#*s1?s1;#l#+s1Ks1B#l#0#>K=s#%?4#m##s#&%s4eS-+S-s$5%#s4z#%#%s4MS-%&s4Z#$#*&#m#+#+S-s#D%#s5&#-#%%s4a#+#*%#m#)#>S-s#K#?CSBSCS(S-s06S^S3S'#:s015#,s$x,#,#,#,#,#,#'#'#'#3#%s5(s4D5s$]+s4F#%#s5>#&#%s4ms4I%&s4z#$#*&#3s5r+s4N#%#s5F#.#%%s5%#+#*%#.S)2033#.Ds4V.D,BSWDDDSESEs$Rs$Rs$Fs$p-#;DDDDDDS&s$Ss$Ss$SS&s$Ks4Ys4Y%6.#1DDJs$TJs$P6.#s5Qs5Qs$D2969.(#.S)5066#1DDJs$XJs$T:2's52s52s$C28780$#<:720'#4Ds4a(Ds1vH#)s1}GEEF#I4D97D&#(D#Hs2#)s2%GEEF#I/s2&GEEF'#(Ds1vH*)s2(GEEF#I(D(Hs1{)s2*GEEF#I/s2+GEEF%#6s2,GEEF(#l#)#s1as1[l#*s23s2/#l#+s2?s26#l#0#AK=s#)B5#m##s#*%s5YS,+S,s#3%#s5n#%#%s5AS,%&s5N#$#*&#m#+#+S,s#H%#s5v#-#%%s5U#+#*%#m#)#>S,s#O#?CSBSCS(S,s1$S\S3S'#:s0{5#,s3f,#,#'#,#'#,#,#,#'#'#'#'#3#%s5{s5-+s5.s#U%#s64#%#%s5cs51%&s5p#$#*&#+s55s#T%#s6;#,#%%s5v#*#*%#.S)0011#.Ds5=;DDDDDDS&s%Fs%Fs%FS&s%>s5>s5>#s#es#]s#R1DDJs%GJs%C3,#s6Ds6Ds%72535,&#.S)2033#1DDJs%KJs%G70's6%s6%s%62545.$#<740.'#4Ds5F(Ds2iH#)s2pGEEF#I7D%s#Q(D#Hs2q)s2sGEEF#I/s2tGEEF&#(Ds2hH))s2vGEEF#I(D(Hs2m)s2xGEEF#I/s2yGEEF%#6s2zGEEF(#l#)#s2Ss2Ml#*s3%s2}#l#+s31s3(#l#0#>K=s#%?4#m##s#&%s6KS++S+s$%%#s6`#%#%s63S+%&s6@#$#*&#m#+#+S+s#F%#s6h#-#%%s6G#+#*%#m#)#>S+s#M#?CSBSCS(S+s1lSZS3S'#:s1d5#,s#L,#'#,#'#'#'#'#3#%s6hs5j&s&9&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#5#+s5|#%#s72#6#%s6as6#%&s6n#$#*&#'s4}'#'#3#+s6+#%#s7=#A#%%s6x#.#*%#.S)s#%0s#&s#&#.Ds63.D,BSWDDDSESEs&Is&Is&=9-#;DDDDDDS&s&Js&Js&JS&s&Bs66s66%9.#1DDJs&KJs&G9.#s7Hs7Hs&;2s#,9s#,.(#.S)8099#1DDJs&OJs&K=2's7)s7)s&:2;:;0$#<=:20'#4Ds6>(Ds3mH#)s3tGEEF#I4D97D&#(D#Hs3v)s3xGEEF#I/s3yGEEF'#(Ds3mH*)s3{GEEF#I(D(Hs3r)s3}GEEF#I/s3~GEEF%#6s4#GEEF(#l#)#s3Xs3Rl#*s4*s4&#l#+s46s4-#l#0#AK=s#,B5#m##s#-%s7PS*+S*s#6%#s7e#%#%s78S*%&s7E#$#*&#m#+#+S*s#Y%#s7m#-#%%s7L#+#*%#m#)#>S*s#`#?CSBSCS(S*s2hSVS3S'#:s2`5#,s$S'#'#,#'#'#'#'#'#'#3#%s7os6h+s6is#U%#s8(#%#%s7Ws6l%&s7d#$#*&#+s6ps#Q%#s8/#,#%%s7j#*#*%#.S)0011#.Ds6x;DDDDDDS&s':s':s':S&s'2s6ys6y#s#es#Zs#O1DDJs';Js'73,#s88s88s'+2535,&#.S)2033#1DDJs'?Js';70's7us7us'*2545.$#<740.'#4Ds7%(Ds4]H#)s4dGEEF#I7D%s#N(D#Hs4e)s4gGEEF#I/s4hGEEF&#(Ds4\H))s4jGEEF#I(D(Hs4a)s4lGEEF#I/s4mGEEF%#6s4nGEEF(#l#)#s4Gs4Al#*s4us4q#l#+s5%s4x#l#0#>K=s#%?4#m##s#&%s8?S%+S%s$%%#s8T#%#%s8'S%%&s84#$#*&#m#+#+S%s#C%#s8\#-#%%s8;#+#*%#m#)#>S%s#J#?CSBSCS(S%s3NSRS3S'#:s3A5#'s%D'#'#'#,#,#,#'#'#'#'#'#3#%s8`s7O&s$G&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#5#+s7y#%#s9B#s#.#%s8qs7|%&s8~#$#*&#'s72'#'#'#'#3#+s8*#%#s9O#s#;#%%s9.#0#*%#.S)s#?0s#@s#@#.Ds82.D,BSWDDDSESEs([s([s(O;-#;DDDDDDS&s(\s(\s(\S&s(Ts85s85%;.#1DDJs(]Js(Y;.#s9Zs9Zs(M2s#F;s#F.(#.S):0;;#1DDJs(aJs(]?2's9;s9;s(L2=<=0$#<?<20'#4Ds8=(Ds6#H#)s6*GEEF#I4D97D&#(D#Hs6,)s6.GEEF#I/s6/GEEF'#(Ds6#H*)s61GEEF#I(D(Hs6()s63GEEF#I/s64GEEF%#6s65GEEF(#l#)#s5js5dl#*s6<s68#l#+s6Hs6?#l#0#AK=s#.B5#m##s#/%s9bS#+S#s#8%#s9w#%#%s9JS#%&s9W#$#*&#m#+#+S#s#w%#s:##-#%%s9^#+#*%#m#)#>S#s#~#?CSBSCS(S#s4cSPS3S'#:s4[5#,s$$'#'#'#'#,#'#'#'#'#3#%s:%s8c+s8ds%g%#s::#%#%s9is8g%&s9v#$#*&#+s8ks%c%#s:A#,#%%s9|#*#*%#.S)0011#.Ds8s;DDDDDDS&s)Ls)Ls)LS&s)Ds8ts8t#s%ws%ls%a1DDJs)MJs)I3,#s:Js:Js)=2535,&#.S)2033#1DDJs)QJs)M70's:+s:+s)<2545.$#<740.'#4Ds8|(Ds6oH#)s6vGEEF#I7D%s%`(D#Hs6w)s6yGEEF#I/s6zGEEF&#(Ds6nH))s6|GEEF#I(D(Hs6s)s6~GEEF#I/s7#GEEF%#6s7$GEEF(#l#)#s6Ys6Sl#*s7+s7'#l#+s77s7.#l#0#>K=s#%?4#m##s#&%s:QR+Rs&7%#s:f#%#%s:9R%&s:F#$#*&#m#+#+Rs#C%#s:n#-#%%s:M#+#*%#m#)#>Rs#J#?CSBSCS(Rs5ISMS3S'#:s5H5#,s%_,#,#,#,#'#'#'#'#3#%s:os9F+s9Gs(I%#s;(#%#%s:Ws9J%&s:d#$#*&#+s9Ns(H%#s;/#,#%%s:j#*#*%#.S)0011#.Ds9V;DDDDDDS&s*:s*:s*:S&s*2s9Ws9W#s(Ys(Qs(F1DDJs*;Js*73,#s;8s;8s*+2535,&#.S)2033#1DDJs*?Js*;70's:us:us**2545.$#<740.'#4Ds9_(Ds7]H#)s7dGEEF#I7D%s(E(D#Hs7e)s7gGEEF#I/s7hGEEF&#(Ds7\H))s7jGEEF#I(D(Hs7a)s7lGEEF#I/s7mGEEF%#6s7nGEEF(#l#)#s7Gs7Al#*s7us7q#l#+s8%s7x#l#0#>K=s#%?4#m##s#&%s;?Q+Qs(u%#s;T#%#%s;'Q%&s;4#$#*&#m#+#+Qs#B%#s;\#-#%%s;;#+#*%#m#)#>Qs#I#?CSBSCS(Qs65SKS3S'#:s645#'s#L'#,#,#,#'#'#'#3#%s;\s:)+s:*s)6%#s;q#%#%s;Ds:-%&s;Q#$#*&#+s:1s)5%#s;x#,#%%s;W#*#*%#.S)0011#.Ds:9;DDDDDDS&s+'s+'s+'S&s*{s::s::#s)Fs)>s)31DDJs+(Js+$3,#s<%s<%s*t2535,&#.S)2033#1DDJs+,Js+(70's;bs;bs*s2545.$#<740.'#4Ds:B(Ds8JH#)s8QGEEF#I7D%s)2(D#Hs8R)s8TGEEF#I/s8UGEEF&#(Ds8IH))s8WGEEF#I(D(Hs8N)s8YGEEF#I/s8ZGEEF%#6s8[GEEF(#l#)#s84s8.l#*s8bs8^#l#+s8ns8e#l#0#>K=s#%?4#m##s#&%s<,P+Ps)b%#s<A#%#%s;pP%&s;}#$#*&#m#+#+Ps#A%#s<I#-#%%s<(#+#*%#m#)#>Ps#H#?CSBSCS(Ps6|SIS3S'#:s6{5#'s<s'#'#'#'#,#'#'#'#'#3#%s<Ks:m&s%~&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#&#5#+s;[#%#s=M#s#N#%s<|s;^%&s=-#$#*&#,s,b'#'#'#3#+s;g#%#s=Y#s#Z#%%s=8#/#*%#.S)s#^0s#_s#_#.Ds;o.D,BSWDDDSESEs,es,es,Y:-#;DDDDDDS&s,fs,fs,fS&s,^s;rs;r%:.#1DDJs,gJs,c:.#s=ds=ds,W2s#e:s#e.(#.S)90::#1DDJs,kJs,g>2's=Es=Es,V2<;<0$#<>;20'#4Ds;z(Ds:-H#)s:4GEEF#I4D97D&#(D#Hs:6)s:8GEEF#I/s:9GEEF'#(Ds:-H*)s:;GEEF#I(D(Hs:2)s:=GEEF#I/s:>GEEF%#6s:?GEEF(#l#)#s9ts9nl#*s:Fs:B#l#+s:Rs:I#l#0#AK=s#-B5#m##s#.%s=lO+Os#7%#s>%#%#%s=TO%&s=a#$#*&#m#+#+Os$8%#s>-#-#%%s=h#+#*%#m#)#>Os$?#?CSBSCS(Os8^SGS3S'#:s8]5#,s(y'#'#,#'#'#'#'#3#%s>-s<G+s<Hs#T%#s>B#%#%s=qs<K%&s=~#$#*&#+s<Os#O%#s>I#,#%%s>(#*#*%#.S)0011#.Ds<W;DDDDDDS&s-Ts-Ts-TS&s-Ls<Xs<X#s#ds#Xs#M1DDJs-UJs-Q3,#s>Rs>Rs-E2535,&#.S)2033#1DDJs-YJs-U70's>3s>3s-D2545.$#<740.'#4Ds<`(Ds:wH#)s:~GEEF#I7D%s#L(D#Hs;#)s;%GEEF#I/s;&GEEF&#(Ds:vH))s;(GEEF#I(D(Hs:{)s;*GEEF#I/s;+GEEF%#6s;,GEEF(#l#)#s:as:[l#*s;3s;/#l#+s;?s;6#l#0#>K=s#%?4#m##s#&%s>YN+Ns$$%#s>n#%#%s>AN%&s>N#$#*&#m#+#+Ns#A%#s>v#-#%%s>U#+#*%#m#)#>Ns#H#?CSBSCS(Ns9ISDS3S'#:s9E5#,s-A,#'#'#,#'#'#'#'#3#+s=,s9T%s>x#5s.i+%#%#s?2#&#%s>a(%&s>n#$#*&#+,s9^%#s?9#-#%%s>t#*#*%#.S)1022#.D4.Ds9gBSWDDDSESEs.Es.Es.9s.{s9h#;DDDDDDS&s.Fs.Fs.FS&s.>77%5s9i#1DDJs.GJs.C5.#s?Ds?Ds.72858.(#.S)4055#1DDJs.KJs.G92's?%s?%s.627670$#<9620'#4Ds=I4Ds9r7D$#(Ds;kH#)s;rGEEF#I7D%&(D#Hs;s)s;uGEEF#I/s;vGEEF&#(Ds;jH))s;xGEEF#I(D(Hs;o)s;zGEEF#I/s;{GEEF%#6s;|GEEF(#l#)#s;Us;Ol#*s<'s<##l#+s<3s<*#l#0#BK=s#)s##6#m##s#*%s?Ms:)+s:*s#3%#s?b#%#%s?5s:-%&s?B#$#*&#m#+#+s:2s#H%#s?j#-#%%s?I#+#*%#m#)#>s:9s#O#?CSBSCS(s::s:8S1S3S'#:s:55#'s-E'#'#,#,#'#'#'#3#+s=ps:G%s?k#+$s#Q%#s@$#%#%s?S'%&s?`#$#*&#++s:P%#s@+#,#%%s?f#*#*%#.S)0011#.D3;DDDDDDS&s/6s/6s/6S&s/.44#s#as:Ys#O1DDJs/7Js/33,#s@4s@4s/'2535,&#.S)2033#1DDJs/;Js/770's?qs?qs/&2545.$#<740.'#4Ds>.7D#s#N(Ds<ZH#)s<aGEEF#I7D%s#Q(D#Hs<b)s<dGEEF#I/s<eGEEF&#(Ds<YH))s<gGEEF#I(D(Hs<^)s<iGEEF#I/s<jGEEF%#6s<kGEEF(#l#)#s<Ds<>l#*s<rs<n#l#+s<~s<u#l#0#?K=s#&@5#m##s#'%s@<s:p+s:qs#~%#s@Q#%#%s@$s:t%&s@1#$#*&#m#+#+s:ys#C%#s@Y#-#%%s@8#+#*%#m#)#>s;$s#J#?CSBSCS(s;%s;#STS3S'#:s:|5#%s@Ps@45s09+s@6#%#s@f#&#%s@9s@9%&s@F#$#*&#3sA?+s@>#%#s@n#.#%%s@M#+#*%#.S)2033#.Ds@F.D,BSWDDDSESEs/zs/zs/ns0L-#;DDDDDDS&s/{s/{s/{S&s/ss@Is@I%6.#1DDJs/|Js/x6.#s@ys@ys/l2969.(#.S)5066#1DDJs0$Js/|:2's@Zs@Zs/k28780$#<:720'#(Ds=AHs=:)s=HGEEF#I4D87Ds==#(D#Hs=J)s=LGEEF#I/s=MGEEF'#(Ds=AHs=A)s=OGEEF#I(D(Hs=F)s=QGEEF#I/s=RGEEF%#6s=SGEEF(#l#)#s=,s=&l#*s=Zs=V#l#+s=fs=]#l#0#@K=s#(A4#m##s#)%sA$L+Ls#2%#sA9#%#%s@hL%&s@u#$#*&#m#+#+Ls#<%#sAA#-#%%s@|#+#*%#m#)#>Ls#C#?CSBSCS(Ls;cS$S3S'#:s;`5#'s>s,#'#'#'#3#%sA>s?>+s??s#L%#sAS#%#%sA&s?B%&sA3#$#*&#+s?Fs#K%#sAZ#,#%%sA9#*#*%#.S)0011#.Ds?N;DDDDDDS&s0es0es0eS&s0]s?Os?O#s#\s#Ts#I1DDJs0fJs0b3,#sAcsAcs0V2535,&#.S)2033#1DDJs0jJs0f70'sADsADs0U2545.$#<740.'#4Ds?W(Ds>,H#)s>3GEEF#I7D%s#I(D#Hs>4)s>6GEEF#I/s>7GEEF&#(Ds>+H))s>9GEEF#I(D(Hs>0)s>;GEEF#I/s><GEEF%#6s>=GEEF(#l#)#s=rs=ll#*s>Ds>@#l#+s>Ps>G#l#0#>K=s#%?4#m##s#&%sAjM+Ms#x%#sB##%#%sARM%&sA_#$#*&#m#+#+Ms#>%#sB+#-#%%sAf#+#*%#m#)#>Ms#E#?CSBSCS(Ms<IKS3S'#8s21s2@s#I#8s23s21s$2#8s25s21s$~#8s27s21s%s#8s29s21s&a#8s2;s21s(F#8s2=s21s)4#8s2?s21s*##8s2As21s*o#8s2Cs21s,7#8s2Es21s-'#8s2Gs21s.-#8s2Is21s.|#8s2Ks21s/q#8s2Ms21s0b#j#=s2O#j#>s2Q#V#S$Kj##s2T#j##s2u#@s2vs2us2W#Kj#>s2x#j#?s2|#V#S$Kj##s3##j##s3F#@s3Gs3Ds3(#Kj#?s3I#j#@s3O#V#S$Kj##s3R#j##s3w#@s3xs3ss3Y#Kj#@s3z#j#As4&#V#S$Kj##s4)#j##s4P#@s4Qs4Js42#Kj#As4S#j#Bs4]#V#S$Kj##s4`#j##s5-#@s5.s5%s4k#Kj#Bs50#j#Cs5<#V#S$Kj##s5?#j##s5j#@s5ks5`s5L#Kj#Cs5m#j#Ds5{#V#S$Kj##s5~#j##s6O#@s6Ps6Cs61#Kj#Ds6R#j#Es6b#V#S$Kj##s6e#j##s78#@s79s7*s6v#Kj#Es7;#j#Fs7M#V#S$Kj##s7P#j##s8%#@s8&s7qs7c#Kj#Fs8(#j#Gs8<#V#S$Kj##s8?#j##s8r#@s8ss8`s8T#Kj#Gs8u#j#Hs9/#V#S$Kj##s92#j##s9g#@s9hs9Ss9I#Kj#Hs9j#j#Is:&#V#S$Kj##s:)#j##s:`#@s:as:Js:B#Kj#Is:c#j#1s:}#V#S$Kj##s;$#j##s;]#@s;^s;Es;?#Kj#1s;`#j#Js;|#V#S$Kj##s<##j##s<^#@s<_s<Ds<@#Kj#Js<a#j#Ks=##V#S$Kj##s=&#j##s>M#@s>Ns=Gs=E#SXUSgSTm#$#l#Ls>]s>Y#j#%s@V#j#MsCh#j#NsCj#j#OsCl#j#PsCn#j#<Tz#j#&sC|##"). Qed.

(* [comment removed for export] *)
Definition XStatics_img_ok : bool :=
  forallb (fun ac : Z * list Z =>
             match image_bytes usegs (fst ac) (8 * length (snd ac))%nat with
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
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.XS.XStatics_img_ok)|] Array.empty "##&###(#'#(#&#)#*#VECDWFCGDm$$##"). Qed.

(* [comment removed for export] *)
Definition HttpCatCells (built : bool) : list cell :=
  if built then [C8 (wz VP_HTTP_ECAT); C8 (wz HTTP_CAT_ID); CB 40 (zeros 40)] else [CB 56 (zeros 56)].
Definition HttpCatGuardCells (built : bool) : list cell :=
  if built then [CB 8 (b8 1 :: b8 1 :: zeros 6)] else [CB 8 (zeros 8)].
Definition HttpCat (m : mem) (built : bool) : Prop :=
  rw_cells usegs m G_HTTP_CAT (HttpCatCells built) /\ rw_cells usegs m G_HTTP_CAT_GUARD (HttpCatGuardCells built).

(* [comment removed for export] *)
Definition CanaryReads (m : mem) : Prop :=
  Lib.PropExec.rdn usegs m (Z_to_bv 64 G_GOT_STACK_CHK) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 G_STACK_CHK_GUARD))
  /\ exists can : Z, Lib.PropExec.rdn usegs m (Z_to_bv 64 G_STACK_CHK_GUARD) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).

End XS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RBL.
  Context {HCEIL : HeapCeil}.

Record rbnode := mkRBN { rbn_parent : Z ; rbn_left : Z ; rbn_right : Z ; rbn_color : Z }.
Definition RBnodeCells (n : rbnode) (pad : list byte) : list cell :=
  [C8 (wz (rbn_parent n)); C8 (wz (rbn_left n)); C8 (wz (rbn_right n)); C4 (wz (rbn_color n)); CB 4 pad].
Definition RBcells (m : mem) (ns : gmap Z rbnode) : Prop :=
  map_Forall (fun (a : Z) (n : rbnode) => exists pad, rw_cells usegs m a (RBnodeCells n pad)) ns.

Record dlnode := mkDLN { dl_next : Z ; dl_prev : Z }.
Definition DLnodeCells (n : dlnode) : list cell := [C8 (wz (dl_next n)); C8 (wz (dl_prev n))].
Definition DLcells (m : mem) (ls : gmap Z dlnode) : Prop :=
  map_Forall (fun (a : Z) (n : dlnode) => rw_cells usegs m a (DLnodeCells n)) ls.

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
Lemma RBcells_lookup : forall m ns a n, RBcells m ns -> ns !! a = Some n -> exists pad, rw_cells usegs m a (RBnodeCells n pad).
Proof. intros m ns a n H L. exact (map_Forall_lookup_1 _ _ _ _ H L). Qed.
Lemma DLcells_lookup : forall m ls a n, DLcells m ls -> ls !! a = Some n -> rw_cells usegs m a (DLnodeCells n).
Proof. intros m ls a n H L. exact (map_Forall_lookup_1 _ _ _ _ H L). Qed.

End RBL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KIT.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma rw_cells_recells : forall m A cs cs',
  rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells usegs m A cs'.
Proof.
  intros m A cs cs' [[WF B] W] WF' EB ES. split; [split|].
  - exact WF'.
  - rewrite EB. exact B.
  - rewrite ES. exact W.
Qed.

(* [comment removed for export] *)
Lemma PMutex_of_zero : forall m a, rw_cells usegs m a PMutexZeroCells -> a mod 4 = 0 -> PMutex m a 0.
Proof.
  intros m a H Ha. split; [| split; [left; reflexivity| exact Ha]].
  eapply rw_cells_recells; [exact H | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.
Lemma PCond_of_zero6 : forall m a, rw_cells usegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> a mod 8 = 0 -> PCond m a 0.
Proof.
  intros m a H Ha. split; [| split; [left; reflexivity| exact Ha]].
  eapply rw_cells_recells; [exact H | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma le8_firstn4 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Lemma C8_read_low4 : forall m A (w : word) cs,
  rw_cells usegs m A (C8 w :: cs) -> ov_read_bytes usegs m (wa A) 4 = Some (le4 w).
Proof.
  intros m A w cs [[WF B] _].
  pose proof (bytes_at_ov_read usegs m A _ 0 4 B) as R. rewrite Z.add_0_r in R.
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
  PMutex m a lk -> munch W m m' -> wmono usegs m m' -> disjoint_from W a SZ_PMUTEX -> PMutex m' a lk.
Proof.
  intros W m m' a lk (C & L & A) MU WM D. split; [| split; assumption].
  unfold PMutexCells, zeros, SZ_PMUTEX in *. xtransport MU WM D.
Qed.

Lemma PCond_transport : forall W m m' a clk,
  PCond m a clk -> munch W m m' -> wmono usegs m m' -> disjoint_from W a SZ_PCOND -> PCond m' a clk.
Proof.
  intros W m m' a clk (C & L & A) MU WM D. split; [| split; assumption].
  unfold PCondCells, zeros, SZ_PCOND in *. xtransport MU WM D.
Qed.

Lemma ErrCode_transport : forall W m m' a E,
  ErrCode m a E -> munch W m m' -> wmono usegs m m' -> disjoint_from W a SZ_EC -> ErrCode m' a E.
Proof.
  intros W m m' a E (C & OK) MU WM D. split; [| exact OK]. unfold ErrCodeCells, SZ_EC in *. xtransport MU WM D.
Qed.

Lemma HttpCat_transport : forall W m m' b,
  HttpCat m b -> munch W m m' -> wmono usegs m m' ->
  disjoint_from W G_HTTP_CAT 56 -> disjoint_from W G_HTTP_CAT_GUARD 8 -> HttpCat m' b.
Proof.
  intros W m m' b (C1 & C2) MU WM D1 D2. unfold HttpCat.
  destruct b; (split; [xtransport MU WM D1 | xtransport MU WM D2]).
Qed.

Lemma FlatBuf_transport : forall W LB m m' a F ds,
  FlatBuf LB m a F ds -> munch W m m' -> wmono usegs m m' -> disjoint_from W a SZ_FB ->
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
  AllocImpl LB m a -> munch W m m' -> wmono usegs m m' -> disjoint_from W a SZ_ALLOCIMPL -> AllocImpl LB m' a.
Proof.
  intros W LB m m' a (p & junk & IN & C) MU WM D. exists p, junk. split; [exact IN|]. unfold SZ_ALLOCIMPL in *. xtransport MU WM D.
Qed.

Lemma Registry_transport : forall W LB m m' r owner first lk,
  Registry LB m r owner first lk -> munch W m m' -> wmono usegs m m' -> disjoint_from W r NEWSZ_REG ->
  Registry LB m' r owner first lk.
Proof.
  intros W LB m m' r owner first lk (p & j0 & j7 & IN & C0 & PM & C1 & C2) MU WM D. exists p, j0, j7.
  unfold NEWSZ_REG, O_REG_MUTEX, O_REG_OWNER, SZ_REG, CookieCells, zeros in *.
  split; [exact IN|]. split; [xtransport MU WM D|]. split.
  { eapply PMutex_transport; [exact PM| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PMUTEX; lia]]. }
  split; xtransport MU WM D.
Qed.

Lemma ConfigSvc_transport : forall W LB m m' c S,
  ConfigSvc LB m c S -> munch W m m' -> wmono usegs m m' -> disjoint_from W c NEWSZ_CFG -> ConfigSvc LB m' c S.
Proof.
  intros W LB m m' c S (p & j4 & j7 & IN & C & E) MU WM D. exists p, j4, j7. split; [exact IN|]. split; [| exact E].
  unfold NEWSZ_CFG, SvcHdrCells, CookieCells, zeros in *. xtransport MU WM D.
Qed.

Lemma StreamSvc_transport : forall W LB m m' v S implb,
  StreamSvc LB m v S implb -> munch W m m' -> wmono usegs m m' -> disjoint_from W v NEWSZ_SSVC -> StreamSvc LB m' v S implb.
Proof.
  intros W LB m m' v S implb (p & j7 & IN & C & E) MU WM D. exists p, j7. split; [exact IN|]. split; [| exact E].
  unfold NEWSZ_SSVC, SvcHdrCells, CookieCells, zeros in *. xtransport MU WM D.
Qed.

Lemma Scheduler_transport : forall W LB m m' s S,
  Scheduler LB m s S -> munch W m m' -> wmono usegs m m' -> disjoint_from W s NEWSZ_SCH -> Scheduler LB m' s S.
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
  ImplBlock LB m b I -> munch W m m' -> wmono usegs m m' -> disjoint_from W b SZ_SPCI_IMPL ->
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
  StateBlock LB m b ioc implb S ds -> munch W m m' -> wmono usegs m m' -> disjoint_from W b SZ_SPCI_STATE ->
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
