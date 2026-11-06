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
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_FUZZ                       : Z := 0xa4af0.   (* [comment removed for export] *)
Definition P_A_STREAM_CTOR                : Z := 0xa547c.   (* [comment removed for export] *)
Definition P_A_STREAM_CLOSE_REMOTE        : Z := 0xa58ec.   (* [comment removed for export] *)
Definition P_A_PARSER_DTOR                : Z := 0xa5d4c.   (* [comment removed for export] *)
Definition P_A_STREAM_DTOR                : Z := 0xa5f20.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_MAKE_SVC_CONFIG            : Z := 0xa6e30.   (* [comment removed for export] *)
Definition P_A_DESTROY_ALLOC_CONFIG       : Z := 0xa7194.   (* [comment removed for export] *)
Definition P_A_CONFIG_SHUTDOWN            : Z := 0xa72c8.   (* [comment removed for export] *)
Definition P_A_CONFIG_GET_VALUE           : Z := 0xa72d0.   (* [comment removed for export] *)
Definition P_A_DEALLOC_OBJ_CONFIG         : Z := 0xa7534.   (* [comment removed for export] *)
Definition P_A_DO_ADD_SERVICE             : Z := 0xa75d8.   (* [comment removed for export] *)
Definition P_A_THROW_INVALID_SERVICE_OWNER : Z := 0xa7b18.   (* [comment removed for export] *)
Definition P_A_THROW_SERVICE_ALREADY_EXISTS : Z := 0xa7b84.   (* [comment removed for export] *)
Definition P_A_DESTROY_ADDED              : Z := 0xa7bf0.   (* [comment removed for export] *)
Definition P_A_STD_THROW_BAD_ARRAY_NEW_LENGTH : Z := 0xa93ec.   (* [comment removed for export] *)
Definition P_A_ALLOCIMPL_DESTROY          : Z := 0xa9438.   (* [comment removed for export] *)
Definition P_A_ALLOCIMPL_ALLOCATE         : Z := 0xa94ac.   (* [comment removed for export] *)
Definition P_A_ALLOCIMPL_DEALLOCATE       : Z := 0xa9880.   (* [comment removed for export] *)
Definition P_A_ALLOCIMPL_BASE_DTOR        : Z := 0xa998c.   (* [comment removed for export] *)
Definition P_A_THROW_BAD_ALLOC            : Z := 0xa9998.   (* [comment removed for export] *)
Definition P_A_ALLOC_OBJ_REGISTRY         : Z := 0xaa218.   (* [comment removed for export] *)
Definition P_A_THROW_SYSTEM_ERROR         : Z := 0xaae9c.   (* [comment removed for export] *)
Definition P_A_MAKE_SVC_SCHED             : Z := 0xaca58.   (* [comment removed for export] *)
Definition P_A_ALLOC_OBJ_SCHED            : Z := 0xacbc4.   (* [comment removed for export] *)
Definition P_A_DESTROY_ALLOC_SCHED        : Z := 0xacd10.   (* [comment removed for export] *)
Definition P_A_SCHED_GET_DEFAULT_TASK     : Z := 0xacd90.   (* [comment removed for export] *)
Definition P_A_SCHED_CTOR                 : Z := 0xacde4.   (* [comment removed for export] *)
Definition P_A_DO_USE_SERVICE             : Z := 0xad9b8.   (* [comment removed for export] *)
Definition P_A_CREATE_CONFIG              : Z := 0xb1038.   (* [comment removed for export] *)
Definition P_A_CONFIG_GET_BOOL            : Z := 0xb13b0.   (* [comment removed for export] *)
Definition P_A_THROW_OUT_OF_RANGE         : Z := 0xb1874.   (* [comment removed for export] *)
Definition P_A_CONFIG_GET_INT             : Z := 0xb2138.   (* [comment removed for export] *)
Definition P_A_OPQUEUE_DTOR               : Z := 0xb45cc.   (* [comment removed for export] *)
Definition P_A_CEM_SCOPED_LOCK            : Z := 0xb48d0.   (* [comment removed for export] *)
Definition P_A_CEM_CTOR                   : Z := 0xb543c.   (* [comment removed for export] *)
Definition P_A_SCHED_DTOR                 : Z := 0xb59c0.   (* [comment removed for export] *)
Definition P_A_SCHED_DELDTOR              : Z := 0xb5c84.   (* [comment removed for export] *)
Definition P_A_SCHED_SHUTDOWN             : Z := 0xb5cb0.   (* [comment removed for export] *)
Definition P_A_POSIX_EVENT_CTOR           : Z := 0xb6298.   (* [comment removed for export] *)
Definition P_A_CONFIG_GET_LONG            : Z := 0xb67a4.   (* [comment removed for export] *)
Definition P_A_POSIX_EVENT_SIGNAL_ALL     : Z := 0xb849c.   (* [comment removed for export] *)
Definition P_A_DEALLOC_OBJ_SCHED          : Z := 0xb9ab0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_PARSER_DTOR_THUNK          : Z := 0xb9b98.   (* [comment removed for export] *)
Definition P_A_ON_REQUEST_IMPL            : Z := 0xb9bc4.   (* [comment removed for export] *)
Definition P_A_ON_RESPONSE_IMPL           : Z := 0xb9be0.   (* [comment removed for export] *)
Definition P_A_ON_FIELD_IMPL              : Z := 0xb9be4.   (* [comment removed for export] *)
Definition P_A_ON_TRAILER_FIELD_IMPL      : Z := 0xb9bec.   (* [comment removed for export] *)
Definition P_A_ON_HEADER_IMPL             : Z := 0xb9ea0.   (* [comment removed for export] *)
Definition P_A_ON_BODY_INIT_IMPL          : Z := 0xb9ec4.   (* [comment removed for export] *)
Definition P_A_ON_BODY_IMPL               : Z := 0xb9f34.   (* [comment removed for export] *)
Definition P_A_ON_CHUNK_HEADER_IMPL       : Z := 0xb9f60.   (* [comment removed for export] *)
Definition P_A_ON_CHUNK_BODY_IMPL         : Z := 0xba1a4.   (* [comment removed for export] *)
Definition P_A_ON_FINISH_IMPL             : Z := 0xba404.   (* [comment removed for export] *)
Definition P_A_FIELDS_DTOR                : Z := 0xba428.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_FIELDS_DELETE_LIST         : Z := 0xba53c.   (* [comment removed for export] *)
Definition P_A_FIELDS_REALLOC_STRING      : Z := 0xba638.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_ON_REQUEST_IMPL_T          : Z := 0xbad98.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_HEADER_SET_METHOD          : Z := 0xbb020.   (* [comment removed for export] *)
Definition P_A_HEADER_SET_VERSION         : Z := 0xbb364.   (* [comment removed for export] *)
Definition P_A_FIELDS_REALLOC_TARGET      : Z := 0xbb6dc.   (* [comment removed for export] *)
Definition P_A_STRING_TO_VERB             : Z := 0xbc200.   (* [comment removed for export] *)
Definition P_A_SV_INDEX                   : Z := 0xbc9d0.   (* [comment removed for export] *)
Definition P_A_SV_REMOVE_PREFIX           : Z := 0xbca88.   (* [comment removed for export] *)
Definition P_A_FIELDS_INSERT              : Z := 0xbcb68.   (* [comment removed for export] *)
Definition P_A_FIELDS_NEW_ELEMENT         : Z := 0xbccb4.   (* [comment removed for export] *)
Definition P_A_FIELDS_INSERT_ELEMENT      : Z := 0xbceec.   (* [comment removed for export] *)
Definition P_A_FIELDS_VALUE_TYPE_CTOR     : Z := 0xbd38c.   (* [comment removed for export] *)
Definition P_A_LIST_ITERATOR_TO           : Z := 0xbd5d0.   (* [comment removed for export] *)
Definition P_A_RB_UPPER_BOUND_LOOP        : Z := 0xbd66c.   (* [comment removed for export] *)
Definition P_A_KEY_COMPARE_SV_VT          : Z := 0xbd76c.   (* [comment removed for export] *)
Definition P_A_FIELDS_FIND_SV             : Z := 0xbd924.   (* [comment removed for export] *)
Definition P_A_LIST_ITERATOR_TO_C         : Z := 0xbd9c8.   (* [comment removed for export] *)
Definition P_A_RB_FIND                    : Z := 0xbda64.   (* [comment removed for export] *)
Definition P_A_RB_LOWER_BOUND_LOOP        : Z := 0xbdb78.   (* [comment removed for export] *)
Definition P_A_KEY_COMPARE_VT_SV          : Z := 0xbdc78.   (* [comment removed for export] *)
Definition P_A_RB_INSERT_BEFORE           : Z := 0xbdd48.   (* [comment removed for export] *)
Definition P_A_RB_REBALANCE               : Z := 0xbdda8.   (* [comment removed for export] *)
Definition P_A_RB_INSERT_COMMIT           : Z := 0xbe29c.   (* [comment removed for export] *)
Definition P_A_RB_PREV_NODE               : Z := 0xbe4d0.   (* [comment removed for export] *)
Definition P_A_RB_IS_HEADER               : Z := 0xbe670.   (* [comment removed for export] *)
Definition P_A_FIELDS_INDEX_F             : Z := 0xbecb4.   (* [comment removed for export] *)
Definition P_A_TOKEN_LIST_EXISTS          : Z := 0xbedb0.   (* [comment removed for export] *)
Definition P_A_FIELDS_FIND_F              : Z := 0xbf0b8.   (* [comment removed for export] *)
Definition P_A_FIELD_TABLE_CTOR           : Z := 0xbf214.   (* [comment removed for export] *)
Definition P_A_FIELD_TABLE_DIGEST         : Z := 0xbf3d0.   (* [comment removed for export] *)
Definition P_A_TOKEN_LIST_ITER_INCR       : Z := 0xbf968.   (* [comment removed for export] *)
Definition P_A_TOKEN_LIST_ITER_CTOR       : Z := 0xbfcb8.   (* [comment removed for export] *)
Definition P_A_READER_PUT                 : Z := 0xbffe0.   (* [comment removed for export] *)
Definition P_A_MB_DYN_PREPARE             : Z := 0xc0454.   (* [comment removed for export] *)
Definition P_A_MB_COMMIT                  : Z := 0xc0894.   (* [comment removed for export] *)
Definition P_A_MB_PREPARE                 : Z := 0xc0b70.   (* [comment removed for export] *)
Definition P_A_MB_LIST_ITERATOR_TO        : Z := 0xc1728.   (* [comment removed for export] *)
Definition P_A_MB_ALLOC                   : Z := 0xc1880.   (* [comment removed for export] *)
Definition P_A_MB_SUBRANGE_CTOR           : Z := 0xc1b20.   (* [comment removed for export] *)
Definition P_A_MB_SUBRANGE_DEREF          : Z := 0xc2e90.   (* [comment removed for export] *)
Definition P_A_BUFFER_COPY_MB             : Z := 0xc3048.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_STD_THROW_LENGTH_ERROR     : Z := 0xc3670.   (* [comment removed for export] *)
Definition P_A_SSVC_MAKE_IMPL             : Z := 0xc36dc.   (* [comment removed for export] *)
Definition P_A_SP_STATE_ARROW             : Z := 0xc38cc.   (* [comment removed for export] *)
Definition P_A_FB_PREPARE                 : Z := 0xc3948.   (* [comment removed for export] *)
Definition P_A_MAKE_SHARED_STATE          : Z := 0xc405c.   (* [comment removed for export] *)
Definition P_A_SP_IMPL_ARROW              : Z := 0xc451c.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_ANYEX_QUERY_CONTEXT        : Z := 0xc4654.   (* [comment removed for export] *)
Definition P_A_THROW_BAD_EXECUTOR         : Z := 0xc4a18.   (* [comment removed for export] *)
Definition P_A_CREATE_SSVC                : Z := 0xc5334.   (* [comment removed for export] *)
Definition P_A_ALLOC_OBJ_SSVC             : Z := 0xc53c4.   (* [comment removed for export] *)
Definition P_A_DESTROY_ALLOC_SSVC         : Z := 0xc5524.   (* [comment removed for export] *)
Definition P_A_MAKE_SHARED_IMPL           : Z := 0xc5648.   (* [comment removed for export] *)
Definition P_A_SSVC_DTOR                  : Z := 0xc57cc.   (* [comment removed for export] *)
Definition P_A_SSVC_DELDTOR               : Z := 0xc5814.   (* [comment removed for export] *)
Definition P_A_SSVC_SHUTDOWN              : Z := 0xc5874.   (* [comment removed for export] *)
Definition P_A_NONCOPYABLE_DTOR           : Z := 0xc5d50.   (* [comment removed for export] *)
Definition P_A_SHCOUNT_CTOR_IMPL          : Z := 0xc5d54.   (* [comment removed for export] *)
Definition P_A_SHCOUNT_DTOR               : Z := 0xc5ed0.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_DTOR             : Z := 0xc6024.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_DELDTOR          : Z := 0xc606c.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_DISPOSE          : Z := 0xc60cc.   (* [comment removed for export] *)
Definition P_A_SPCB_DESTROY               : Z := 0xc60d4.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_GET_DEL          : Z := 0xc612c.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_GET_LDEL         : Z := 0xc6188.   (* [comment removed for export] *)
Definition P_A_SPCI_IMPL_GET_UDEL         : Z := 0xc6190.   (* [comment removed for export] *)
Definition P_A_SPMSD_IMPL_DESTROY         : Z := 0xc6198.   (* [comment removed for export] *)
Definition P_A_VEC_READOP_RESERVE         : Z := 0xc65f0.   (* [comment removed for export] *)
Definition P_A_VEC_READOP_THROW_LEN       : Z := 0xc66cc.   (* [comment removed for export] *)
Definition P_A_SPLITBUF_READOP_DTOR       : Z := 0xc6a70.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_VEC_READOP_DESTROY         : Z := 0xc7388.   (* [comment removed for export] *)
Definition P_A_DEALLOC_OBJ_SSVC           : Z := 0xc760c.   (* [comment removed for export] *)
Definition P_A_SHCOUNT_CTOR_STATE         : Z := 0xc76b0.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_DTOR            : Z := 0xc782c.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_DELDTOR         : Z := 0xc78dc.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_DISPOSE         : Z := 0xc7974.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_GET_DEL         : Z := 0xc7a04.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_GET_LDEL        : Z := 0xc7a60.   (* [comment removed for export] *)
Definition P_A_SPCI_STATE_GET_UDEL        : Z := 0xc7a68.   (* [comment removed for export] *)
Definition P_A_STATE_DTOR                 : Z := 0xc7a70.   (* [comment removed for export] *)
Definition P_A_ANYEX_COPY                 : Z := 0xc7eb8.   (* [comment removed for export] *)
Definition P_A_ANYEX_MOVE                 : Z := 0xc8028.   (* [comment removed for export] *)
Definition P_A_SPLITBUF_STATEP_DTOR       : Z := 0xca138.   (* [comment removed for export] *)
Definition P_A_VEC_STATEP_THROW_LEN       : Z := 0xca250.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_ANYEX_FN_DESTROY           : Z := 0xcbca8.   (* [comment removed for export] *)
Definition P_A_ANYEX_FN_COPY              : Z := 0xcbcac.   (* [comment removed for export] *)
Definition P_A_ANYEX_FN_MOVE              : Z := 0xcbd20.   (* [comment removed for export] *)
Definition P_A_ANYEX_FN_TARGET            : Z := 0xcbd94.   (* [comment removed for export] *)
Definition P_A_ANYEX_FN_QUERY_CTX         : Z := 0xcbd98.   (* [comment removed for export] *)
Definition P_A_STREAM_CLOSE               : Z := 0xce744.   (* [comment removed for export] *)
Definition P_A_STATE_REMOVE               : Z := 0xcef40.   (* [comment removed for export] *)
Definition P_A_SYNC_READ_OP               : Z := 0xcf464.   (* [comment removed for export] *)
Definition P_A_HTTP_READ_SOME             : Z := 0xcf5f0.   (* [comment removed for export] *)
Definition P_A_FB_DYN_PREPARE             : Z := 0xcffd4.   (* [comment removed for export] *)
Definition P_A_STREAM_READ_SOME           : Z := 0xd0184.   (* [comment removed for export] *)
Definition P_A_BP_PUT_EOF                 : Z := 0xd0ca8.   (* [comment removed for export] *)
Definition P_A_BP_PUT                     : Z := 0xd0ed0.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_START_LINE        : Z := 0xd19e4.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_FIELDS            : Z := 0xd1bac.   (* [comment removed for export] *)
Definition P_A_BP_FINISH_HEADER           : Z := 0xd1d70.   (* [comment removed for export] *)
Definition P_A_BP_CONTENT_LENGTH          : Z := 0xd21d0.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_BODY              : Z := 0xd2330.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_BODY_TO_EOF       : Z := 0xd2588.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_CHUNK_HEADER      : Z := 0xd2780.   (* [comment removed for export] *)
Definition P_A_BP_INNER_PARSE_START_LINE  : Z := 0xd3298.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_VERSION           : Z := 0xd3a88.   (* [comment removed for export] *)
Definition P_A_BP_INNER_PARSE_FIELDS      : Z := 0xd40cc.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_FIELD             : Z := 0xd477c.   (* [comment removed for export] *)
Definition P_A_BP_DO_FIELD                : Z := 0xd52d0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_STRING_TO_FIELD            : Z := 0xd65b0.   (* [comment removed for export] *)
Definition P_A_FIELD_TABLE_EQUALS         : Z := 0xd66ec.   (* [comment removed for export] *)
Definition P_A_VALIDATE_OPT_TOKEN_LIST    : Z := 0xd687c.   (* [comment removed for export] *)
Definition P_A_BP_DO_FIELD_LAMBDA         : Z := 0xd694c.   (* [comment removed for export] *)
Definition P_A_OPT_TOKEN_LIST_INCR        : Z := 0xd6ee4.   (* [comment removed for export] *)
Definition P_A_BP_PARSE_CHUNK_EXT         : Z := 0xd73f0.   (* [comment removed for export] *)
Definition P_A_EC_ASSIGN_HTTP             : Z := 0xd7b40.   (* [comment removed for export] *)
Definition P_A_READ_SIZE_FB               : Z := 0xd7ca4.   (* [comment removed for export] *)
Definition P_A_CXA_GUARD_ACQUIRE          : Z := 0xd7fe8.   (* [comment removed for export] *)
Definition P_A_CXA_GUARD_RELEASE          : Z := 0xd8038.   (* [comment removed for export] *)
Definition P_A_STD_TERMINATE              : Z := 0xd8068.   (* [comment removed for export] *)
Definition P_A_OPDEL                      : Z := 0xf48c4.   (* [comment removed for export] *)
Definition P_A_OPDEL2                     : Z := 0xf48c8.   (* [comment removed for export] *)
Definition P_A_OPDEL_ARR                  : Z := 0xf48cc.   (* [comment removed for export] *)
Definition P_A_STD_ALIGN                  : Z := 0xf61c8.   (* [comment removed for export] *)
Definition P_A_STD_THROW_SYSTEM_ERROR     : Z := 0xfa1c4.   (* [comment removed for export] *)
Definition P_A_CV_DTOR                    : Z := 0xfa328.   (* [comment removed for export] *)
Definition P_A_CV_NOTIFY_ALL              : Z := 0xfa360.   (* [comment removed for export] *)
Definition P_A_CV_WAIT                    : Z := 0xfa37c.   (* [comment removed for export] *)
Definition P_A_MTX_DTOR                   : Z := 0xfa4f8.   (* [comment removed for export] *)
Definition P_A_MTX_LOCK                   : Z := 0xfa514.   (* [comment removed for export] *)
Definition P_A_MTX_UNLOCK                 : Z := 0xfa55c.   (* [comment removed for export] *)
Definition P_A_ERRNO_LOCATION             : Z := 0x1032dc.   (* [comment removed for export] *)
Definition P_A_ASSERT_FAIL                : Z := 0x1033d4.   (* [comment removed for export] *)
Definition P_A_FREE                       : Z := 0x74540.   (* [comment removed for export] *)
Definition P_A_MALLOC                     : Z := 0x74544.   (* [comment removed for export] *)
Definition P_A_TOWRITE                    : Z := 0x109adc.   (* [comment removed for export] *)
Definition P_A_FWRITEX                    : Z := 0x109b30.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_VFPRINTF                   : Z := 0x109fc4.   (* [comment removed for export] *)
Definition P_A_PRINTF_CORE                : Z := 0x10a174.   (* [comment removed for export] *)
Definition P_A_POP_ARG                    : Z := 0x10afa4.   (* [comment removed for export] *)
Definition P_A_PAD                        : Z := 0x10b0d8.   (* [comment removed for export] *)
Definition P_A_VSNPRINTF                  : Z := 0x10f76c.   (* [comment removed for export] *)
Definition P_A_SN_WRITE                   : Z := 0x10f838.   (* [comment removed for export] *)
Definition P_A_SHLIM                      : Z := 0x10c9fc.   (* [comment removed for export] *)
Definition P_A_SHGETC                     : Z := 0x10ca34.   (* [comment removed for export] *)
Definition P_A_STRTOLL                    : Z := 0x110f50.   (* [comment removed for export] *)
Definition P_A_INTSCAN                    : Z := 0x10f178.   (* [comment removed for export] *)
Definition P_A_BCMP                       : Z := 0x1119b4.   (* [comment removed for export] *)
Definition P_A_MEMCHR                     : Z := 0x1119b8.   (* [comment removed for export] *)
Definition P_A_MEMCMP                     : Z := 0x111a84.   (* [comment removed for export] *)
Definition P_A_MEMCPY                     : Z := 0x111ab4.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_A_MEMSET                     : Z := 0x111eb8.   (* [comment removed for export] *)
Definition P_A_STRCMP                     : Z := 0x1120cc.   (* [comment removed for export] *)
Definition P_A_STRLEN                     : Z := 0x11219c.   (* [comment removed for export] *)
Definition P_A_PTHREAD_COND_BROADCAST     : Z := 0x112a68.   (* [comment removed for export] *)
Definition P_A_PTHREAD_COND_DESTROY       : Z := 0x112adc.   (* [comment removed for export] *)
Definition P_A_PTHREAD_COND_INIT          : Z := 0x112ca0.   (* [comment removed for export] *)
Definition P_A_PRIVATE_COND_SIGNAL        : Z := 0x113444.   (* [comment removed for export] *)
Definition P_A_PTHREAD_CONDATTR_DESTROY   : Z := 0x1138d4.   (* [comment removed for export] *)
Definition P_A_PTHREAD_CONDATTR_INIT      : Z := 0x1138dc.   (* [comment removed for export] *)
Definition P_A_PTHREAD_CONDATTR_SETCLOCK  : Z := 0x1138e8.   (* [comment removed for export] *)
Definition P_A_PTHREAD_MUTEX_DESTROY      : Z := 0x114a1c.   (* [comment removed for export] *)
Definition P_A_PTHREAD_MUTEX_INIT         : Z := 0x114a44.   (* [comment removed for export] *)
Definition P_A_PTHREAD_MUTEX_LOCK         : Z := 0x114ac4.   (* [comment removed for export] *)
Definition P_A_PTHREAD_MUTEX_UNLOCK       : Z := 0x114fb0.   (* [comment removed for export] *)
Definition P_A_VM_WAIT                    : Z := 0x115c0c.   (* [comment removed for export] *)
Definition P_A_OPNEW                      : Z := 0x118750.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ARVT_ALLOCIMPL       : Z := 0x11a2f8.   (* [comment removed for export] *)
Definition AVP_ALLOCIMPL        : Z := 0x11a308.
Definition AVS_ALLOCIMPL_0      : Z := 0xa9438.
Definition AVS_ALLOCIMPL_8      : Z := 0xa94ac.
Definition AVS_ALLOCIMPL_16     : Z := 0xa9880.
Definition AVS_ALLOCIMPL_24     : Z := 0xa998c.
Definition AVS_ALLOCIMPL_32     : Z := 0xa9990.
Definition ARVT_CONFIG_SVC      : Z := 0x119f98.   (* [comment removed for export] *)
Definition AVP_CONFIG_SVC       : Z := 0x119fa8.
Definition AVS_CONFIG_SVC_0     : Z := 0xc5d50.
Definition AVS_CONFIG_SVC_8     : Z := 0xa72c0.
Definition AVS_CONFIG_SVC_16    : Z := 0xa72c8.
Definition AVS_CONFIG_SVC_24    : Z := 0xa72cc.
Definition AVS_CONFIG_SVC_32    : Z := 0xa72d0.
Definition ARVT_SCHED           : Z := 0x11a6d0.   (* [comment removed for export] *)
Definition AVP_SCHED            : Z := 0x11a6e0.
Definition AVS_SCHED_0          : Z := 0xb59c0.
Definition AVS_SCHED_8          : Z := 0xb5c84.
Definition AVS_SCHED_16         : Z := 0xb5cb0.
Definition AVS_SCHED_24         : Z := 0xa72cc.
Definition ARVT_SSVC            : Z := 0x11b650.   (* [comment removed for export] *)
Definition AVP_SSVC             : Z := 0x11b660.
Definition AVS_SSVC_0           : Z := 0xc57cc.
Definition AVS_SSVC_8           : Z := 0xc5814.
Definition AVS_SSVC_16          : Z := 0xc5874.
Definition AVS_SSVC_24          : Z := 0xa72cc.
Definition ARVT_SPCI_IMPL       : Z := 0x11b6b0.   (* [comment removed for export] *)
Definition AVP_SPCI_IMPL        : Z := 0x11b6c0.
Definition AVS_SPCI_IMPL_0      : Z := 0xc6024.
Definition AVS_SPCI_IMPL_8      : Z := 0xc606c.
Definition AVS_SPCI_IMPL_16     : Z := 0xc60cc.
Definition AVS_SPCI_IMPL_24     : Z := 0xc60d4.
Definition AVS_SPCI_IMPL_32     : Z := 0xc612c.
Definition AVS_SPCI_IMPL_40     : Z := 0xc6188.
Definition AVS_SPCI_IMPL_48     : Z := 0xc6190.
Definition ARVT_SPCI_STATE      : Z := 0x11b720.   (* [comment removed for export] *)
Definition AVP_SPCI_STATE       : Z := 0x11b730.
Definition AVS_SPCI_STATE_0     : Z := 0xc782c.
Definition AVS_SPCI_STATE_8     : Z := 0xc78dc.
Definition AVS_SPCI_STATE_16    : Z := 0xc7974.
Definition AVS_SPCI_STATE_24    : Z := 0xc60d4.
Definition AVS_SPCI_STATE_32    : Z := 0xc7a04.
Definition AVS_SPCI_STATE_40    : Z := 0xc7a60.
Definition AVS_SPCI_STATE_48    : Z := 0xc7a68.
Definition ARVT_PARSER          : Z := 0x11a7b8.   (* [comment removed for export] *)
Definition AVP_PARSER           : Z := 0x11a7c8.
Definition AVS_PARSER_0         : Z := 0xa5d4c.
Definition AVS_PARSER_8         : Z := 0xb9b98.
Definition AVS_PARSER_16        : Z := 0xb9bc4.
Definition AVS_PARSER_24        : Z := 0xb9be0.
Definition AVS_PARSER_32        : Z := 0xb9be4.
Definition AVS_PARSER_40        : Z := 0xb9bec.
Definition AVS_PARSER_48        : Z := 0xb9ea0.
Definition AVS_PARSER_56        : Z := 0xb9ec4.
Definition AVS_PARSER_64        : Z := 0xb9f34.
Definition AVS_PARSER_72        : Z := 0xb9f60.
Definition AVS_PARSER_80        : Z := 0xba1a4.
Definition AVS_PARSER_88        : Z := 0xba404.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARVT_SYSTEM_ECAT     : Z := 0x119d40.   (* [comment removed for export] *)
Definition AVP_SYSTEM_ECAT      : Z := 0x119d50.
Definition AVS_SYSTEM_ECAT_0    : Z := 0xa66e8.
Definition AVS_SYSTEM_ECAT_8    : Z := 0xa4484.
Definition AVS_SYSTEM_ECAT_16   : Z := 0xa6120.
Definition AVS_SYSTEM_ECAT_24   : Z := 0xa62bc.
Definition AVS_SYSTEM_ECAT_32   : Z := 0xa66f4.
Definition AVS_SYSTEM_ECAT_40   : Z := 0xa673c.
Definition AVS_SYSTEM_ECAT_48   : Z := 0xa65dc.
Definition ARVT_GENERIC_ECAT    : Z := 0x119ce0.   (* [comment removed for export] *)
Definition AVP_GENERIC_ECAT     : Z := 0x119cf0.
Definition AVS_GENERIC_ECAT_0   : Z := 0xa65e4.
Definition AVS_GENERIC_ECAT_8   : Z := 0xa4878.
Definition AVS_GENERIC_ECAT_16  : Z := 0xa6120.
Definition AVS_GENERIC_ECAT_24  : Z := 0xa62bc.
Definition AVS_GENERIC_ECAT_32  : Z := 0xa443c.
Definition AVS_GENERIC_ECAT_40  : Z := 0xa65f0.
Definition AVS_GENERIC_ECAT_48  : Z := 0xa65dc.
Definition ARVT_MISC_ECAT       : Z := 0x119ec0.   (* [comment removed for export] *)
Definition AVP_MISC_ECAT        : Z := 0x119ed0.

(* [comment removed for export] *)
Definition AT_ANYEX_TARGET_FNS      : Z := 0x11b828.   (* [comment removed for export] *)
Definition AT_ANYEX_OBJECT_FNS      : Z := 0x11b8e0.   (* [comment removed for export] *)
Definition AT_ANYEX_PROP_FNS        : Z := 0x11b900.   (* [comment removed for export] *)
Definition AT_ANYEX_PROP_FNS_VOID   : Z := 0x11b780.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AT_ANYEX_TARGET_FNS_words : list Z := [0xca350; 0xca35c; 0xca54c; 0x0].
Definition AT_ANYEX_OBJECT_FNS_words : list Z := [0xcbca8; 0xcbcac; 0xcbd20; 0xcbd94].
Definition AT_ANYEX_PROP_FNS_words : list Z := [0xcbd98; 0xcbda0; 0xcbe10; 0xcbe80; 0xcbe88; 0xcbf8c; 0xcc090; 0xcc098; 0xcc108; 0xcc20c; 0xcc214; 0xcc284; 0xcc2a0; 0xcc2a8; 0xcc318; 0xcc418; 0xcc420; 0xcc490; 0xcc594; 0xcc59c; 0xcc60c].
Definition AT_ANYEX_PROP_FNS_VOID_words : list Z := [0xc81c0; 0xc81c4; 0xc81e0; 0xc81fc; 0xc8200; 0xc821c; 0xc8238; 0xc823c; 0xc8258; 0xc8274; 0xc8278; 0xc8294; 0xc82b0; 0xc82b4; 0xc82d0; 0xc82ec; 0xc82f0; 0xc830c; 0xc8328; 0xc832c; 0xc8348].

(* [comment removed for export] *)
Definition AG_EXF_IN_CALLBACK       : Z := 0x65fe14.   (* [comment removed for export] *)
Definition AG_EXF_EMPTY             : Z := 0x65fe20.   (* [comment removed for export] *)
Definition AG_ASIO_SYSTEM_CAT       : Z := 0x65fe40.   (* [comment removed for export] *)
Definition AG_ASIO_NETDB_CAT        : Z := 0x65fe50.   (* [comment removed for export] *)
Definition AG_ASIO_ADDRINFO_CAT     : Z := 0x65fe60.   (* [comment removed for export] *)
Definition AG_ASIO_MISC_CAT         : Z := 0x65fe70.   (* [comment removed for export] *)
Definition AG_CALLSTACK_TOP_GUARD   : Z := 0x65fe88.   (* [comment removed for export] *)
Definition AG_ID_CONFIG             : Z := 0x65fe90.   (* [comment removed for export] *)
Definition AG_ID_SCHED              : Z := 0x65fea0.   (* [comment removed for export] *)
Definition AG_ID_REACTOR            : Z := 0x65feb0.   (* [comment removed for export] *)
Definition AG_ID_SSVC               : Z := 0x65fec0.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AG_FIELD_TABLE           : Z := 0x65ff10.   (* [comment removed for export] *)
Definition AG_FIELD_TABLE_GUARD     : Z := 0x660c88.   (* [comment removed for export] *)
Definition AG_SYSTEM_CAT_INST       : Z := 0x123d30.   (* [comment removed for export] *)
Definition AG_GENERIC_CAT_INST      : Z := 0x123e48.   (* [comment removed for export] *)
Definition AG_INTEROP_CAT_INST      : Z := 0x123e10.   (* [comment removed for export] *)
Definition AG_MISC_CAT_INST         : Z := 0x123dd8.   (* [comment removed for export] *)
Definition AG_STACK_CHK_GUARD       : Z := 0x681830.   (* [comment removed for export] *)
Definition AG_GOT_STACK_CHK         : Z := 0x1203f0.   (* [comment removed for export] *)
Definition AG_ERRNO                 : Z := 0x66174c.   (* [comment removed for export] *)
Definition AG_TP                    : Z := 0x6617f0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AW_SYSTEM_CAT_VPTR     : Z := 0x119d50.   (* [comment removed for export] *)
Definition W_SYSTEM_CAT_ID : Z := 0xb2ab117a257edfd1.
Definition AW_NETDB_CAT_VPTR      : Z := 0x119e10.   (* [comment removed for export] *)
Definition W_NETDB_CAT_ID : Z := 0x0.
Definition AW_ADDRINFO_CAT_VPTR   : Z := 0x119e70.   (* [comment removed for export] *)
Definition W_ADDRINFO_CAT_ID : Z := 0x0.
Definition AW_MISC_CAT_VPTR       : Z := 0x119ed0.   (* [comment removed for export] *)
Definition W_MISC_CAT_ID : Z := 0x0.
Definition AW_INTEROP_CAT_VPTR    : Z := 0x119db0.   (* [comment removed for export] *)
Definition W_INTEROP_CAT_ID : Z := 0xb2ab117a257edfd2.
Definition AW_GENERIC_CAT_VPTR    : Z := 0x119cf0.   (* [comment removed for export] *)
Definition W_GENERIC_CAT_ID : Z := 0xb2ab117a257edfd0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CAT_ID_SYSGEN_SHR1 : Z := 0x595588bd12bf6fe8.   (* [comment removed for export] *)
Definition ATI_NAME_CONFIG        : Z := 0x25380.   (* [comment removed for export] *)
Definition ATI_NAME_SCHED         : Z := 0x25a94.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AL_STR_SCHEDULER           : Z := 0x25200.   (* [comment removed for export] *)
Definition AL_STR_REACTOR             : Z := 0x25300.   (* [comment removed for export] *)
Definition AL_STR_IO_LOCKING          : Z := 0x25320.   (* [comment removed for export] *)
Definition AL_STR_REG_LOCKING         : Z := 0x25340.   (* [comment removed for export] *)
Definition AL_STR_CONCURRENCY_HINT    : Z := 0x25220.   (* [comment removed for export] *)
Definition AL_STR_LOCKING             : Z := 0x252c0.   (* [comment removed for export] *)
Definition AL_STR_ONE                 : Z := 0x25260.   (* [comment removed for export] *)
Definition AL_STR_ZERO                : Z := 0x252e0.   (* [comment removed for export] *)
Definition AL_STR_MINUS_ONE           : Z := 0x25280.   (* [comment removed for export] *)
Definition AL_STR_FMT_D               : Z := 0x252a0.   (* [comment removed for export] *)
Definition AL_STR_ASSUME_CONT         : Z := 0x25e80.   (* [comment removed for export] *)
Definition AL_STR_SPIN                : Z := 0x25ec0.   (* [comment removed for export] *)
Definition AL_STR_TASK_USEC           : Z := 0x25f00.   (* [comment removed for export] *)
Definition AL_STR_WAIT_USEC           : Z := 0x25f20.   (* [comment removed for export] *)
Definition AL_EXECUTION_CONTEXT_PROP  : Z := 0x29360.   (* [comment removed for export] *)
Definition AL_TYPEID_CONFIG           : Z := 0x11a078.   (* [comment removed for export] *)
Definition AL_TYPEID_SCHED            : Z := 0x11a600.   (* [comment removed for export] *)

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
Definition AErrCode (m : mem) (a : Z) (E : ecv) : Prop := rw_cells bsegs m a (ErrCodeCells E) /\ ec_ok E.

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
  rw_cells bsegs m a (FlatBufCells F) /\ fb_ok LB F /\ zlength ds = fb_size F
  /\ (F <> FB_empty -> exists pre junk,
        rw_cells bsegs m (fb_begin F) [CB (Z.to_nat (fb_in F - fb_begin F)) pre; CB (length ds) ds;
                                     CB (Z.to_nat (fb_end F - fb_out F)) junk])
  /\ (F <> FB_empty -> addressable m (fb_begin F) (fb_cap F)).                               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PMutexCells (lk : Z) : list cell := [CB 4 (zeros 4); C4 (wz lk); CB 32 (zeros 32)].
Definition APMutex (m : mem) (a : Z) (lk : Z) : Prop := rw_cells bsegs m a (PMutexCells lk) /\ (lk = 0 \/ lk = EBUSY) /\ a mod 4 = 0.
(* [comment removed for export] *)
Definition PMutexZeroCells : list cell := [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].

(* [comment removed for export] *)
Definition PCondCells (clk : Z) : list cell := [CB 16 (zeros 16); C4 (wz clk); CB 12 (zeros 12); C4 (wz 0); CB 4 (zeros 4); C8 (wz 0)].
Definition APCond (m : mem) (a : Z) (clk : Z) : Prop := rw_cells bsegs m a (PCondCells clk) /\ (clk = 0 \/ clk = CLOCK_MONOTONIC) /\ a mod 8 = 0.

(* [comment removed for export] *)
Record svch := mkSVC { sv_vptr : Z ; sv_ti : Z ; sv_id : Z ; sv_owner : Z ; sv_next : Z ; sv_destroy : Z }.
Definition SvcHdrCells (S : svch) : list cell :=
  [C8 (wz (sv_vptr S)); C8 (wz (sv_ti S)); C8 (wz (sv_id S)); C8 (wz (sv_owner S)); C8 (wz (sv_next S)); C8 (wz (sv_destroy S))].

(* [comment removed for export] *)
Definition CookieCells (junk7 : list byte) : list cell := [CB 8 (zeros 8); CB 7 junk7].

(* [comment removed for export] *)
Definition AAllocImpl (LB : list block) (m : mem) (a : Z) : Prop :=
  exists p junk, In (p, a, SZ_ALLOCIMPL) LB /\ rw_cells bsegs m a [C8 (wz AVP_ALLOCIMPL); CB 8 junk]
  /\ rblock_range a SZ_ALLOCIMPL /\ addressable m a SZ_ALLOCIMPL.                            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ARegistry (LB : list block) (m : mem) (r : Z) (owner first lk : Z) : Prop :=
  exists p j0 j7, In (p, r, NEWSZ_REG) LB
  /\ rw_cells bsegs m r [CB 8 j0]
  /\ APMutex m (r + O_REG_MUTEX) lk
  /\ rw_cells bsegs m (r + O_REG_OWNER) [C8 (wz owner); C8 (wz first)]
  /\ rw_cells bsegs m (r + SZ_REG) (CookieCells j7)
  /\ rblock_range r NEWSZ_REG /\ addressable m r NEWSZ_REG.                                  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AConfigSvc (LB : list block) (m : mem) (c : Z) (S : svch) : Prop :=
  exists p j4 j7, In (p, c, NEWSZ_CFG) LB
  /\ rw_cells bsegs m c (SvcHdrCells S ++ [C4 (wz (2^32 - 1)); CB 4 j4] ++ CookieCells j7)
  /\ sv_vptr S = AVP_CONFIG_SVC /\ sv_destroy S = P_A_DESTROY_ALLOC_CONFIG
  /\ rblock_range c NEWSZ_CFG /\ addressable m c NEWSZ_CFG.                                  (* [comment removed for export] *)

(* [comment removed for export] *)
Record schv := mkSCH { sch_hdr : svch ; sch_lk : Z ; sch_stopped : Z ; sch_shutdown : Z }.
Definition AScheduler (LB : list block) (m : mem) (s : Z) (S : schv) : Prop :=
  exists p j50 jm j109 je jt j219 j7, In (p, s, NEWSZ_SCH) LB
  /\ rw_cells bsegs m s (SvcHdrCells (sch_hdr S))
  /\ rw_cells bsegs m (s + O_SCH_ONE_THREAD) [CB 2 [b8 0; b8 0]; CB 6 j50]           (* [comment removed for export] *)
  /\ rw_cells bsegs m (s + O_SCH_MUTEX) [CB 8 jm]                                     (* [comment removed for export] *)
  /\ APMutex m (s + O_SCH_PMUTEX) (sch_lk S)                                            (* [comment removed for export] *)
  /\ rw_cells bsegs m (s + O_SCH_SPIN) [C4 (wz 0); CB 1 [b8 1]; CB 3 j109]            (* [comment removed for export] *)
  /\ rw_cells bsegs m (s + O_SCH_EVENT) [CB 8 je]                                     (* [comment removed for export] *)
  /\ APCond m (s + O_SCH_COND) CLOCK_MONOTONIC                                          (* [comment removed for export] *)
  /\ rw_cells bsegs m (s + O_SCH_EVSTATE)
       [C8 (wz 0);                                   (* [comment removed for export] *)
        C8 (wz 0); C8 (wz P_A_SCHED_GET_DEFAULT_TASK); (* [comment removed for export] *)
        C8 (wz 0); C8 (wz 0); C4 (wz 0); CB 4 jt;    (* [comment removed for export] *)
        CB 3 [b8 1; b8 (sch_stopped S); b8 (sch_shutdown S)]; CB 5 j219;   (* [comment removed for export] *)
        C8 (wz 0);                                   (* [comment removed for export] *)
        C8 (wz 0); C8 (wz 0);                        (* [comment removed for export] *)
        C8 (wz u64max); C8 (wz u64max);              (* [comment removed for export] *)
        C8 (wz 0)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m (s + SZ_SCH) (CookieCells j7)
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
  /\ rw_cells bsegs m b (SpcHdrCells (im_hdr I) j7) /\ spc_ok (im_hdr I) /\ spc_vptr (im_hdr I) = AVP_SPCI_IMPL
  /\ APMutex m (b + O_SPC_STORAGE + O_IMPL_MUTEX) (im_lk I)
  /\ rw_cells bsegs m (b + O_SPC_STORAGE + O_IMPL_VEC_BEGIN)
       [C8 (wz (im_vb I)); C8 (wz (im_vb I + 8 * zlength (im_states I))); C8 (wz (im_vb I + 8 * im_vcap I))]
  /\ zlength (im_states I) <= im_vcap I
  /\ ((im_vcap I = 0 /\ im_vb I = 0)
      \/ (exists q junk, In (q, im_vb I, 8 * im_vcap I) LB /\ rblock_range (im_vb I) (8 * im_vcap I) /\ 0 < im_vcap I
           /\ rw_cells bsegs m (im_vb I) [CB (8 * length (im_states I)) (flat_map le8z (im_states I));
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
  /\ rw_cells bsegs m b (SpcHdrCells (st_hdr S) j7) /\ spc_ok (st_hdr S) /\ spc_vptr (st_hdr S) = AVP_SPCI_STATE
  /\ rw_cells bsegs m (b + 32 + O_ST_EXEC) (AnyExecCells (b + 32 + O_ST_EXEC) ioc j16)
  /\ rw_cells bsegs m (b + 32 + O_ST_WP_PX) [C8 (wz (implb + O_SPC_STORAGE)); C8 (wz implb)]
  /\ APMutex m (b + 32 + O_ST_MUTEX) (st_lk S)
  /\ AFlatBuf LB m (b + 32 + O_ST_FB) (st_fb S) ds
  /\ APCond m (b + 32 + O_ST_CV) 0
  /\ rw_cells bsegs m (b + 32 + O_ST_OP)
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
  /\ rw_cells bsegs m v (SvcHdrCells S ++ [C8 (wz (implb + O_SPC_STORAGE)); C8 (wz implb)] ++ CookieCells j7)
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
  rw_cells bsegs m ioc (IoCtxCells allocb regb schedb)
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
  rw_cells bsegs m ioc (IoCtxCells allocb regb schedb)
  /\ rw_cells bsegs m bs (BasicStreamCells stateb)
  /\ AAllocImpl LB m allocb
  /\ ARegistry LB m regb ioc ssvcb 0
  /\ AConfigSvc LB m cfgb (mkSVC AVP_CONFIG_SVC AL_TYPEID_CONFIG 0 ioc 0 P_A_DESTROY_ALLOC_CONFIG)
  /\ AScheduler LB m schedb (mkSCH (mkSVC AVP_SCHED AL_TYPEID_SCHED 0 ioc cfgb P_A_DESTROY_ALLOC_SCHED) 0 0 0)
  /\ AStreamSvc LB m ssvcb (mkSVC AVP_SSVC 0 AG_ID_SSVC ioc schedb P_A_DESTROY_ALLOC_SSVC) implb
  /\ AImplBlockV LB m implb 1 2 [stateb + O_SPC_STORAGE] 1
  /\ AStateBlock LB m stateb ioc implb (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 F code nread nread_bytes) ds.
(* [comment removed for export] *)
Definition AIoWorld4 (LB : list block) (m : mem) (ioc allocb regb cfgb schedb ssvcb implb : Z) : Prop :=
  rw_cells bsegs m ioc (IoCtxCells allocb regb schedb)
  /\ AAllocImpl LB m allocb
  /\ ARegistry LB m regb ioc ssvcb 0
  /\ AConfigSvc LB m cfgb (mkSVC AVP_CONFIG_SVC AL_TYPEID_CONFIG 0 ioc 0 P_A_DESTROY_ALLOC_CONFIG)
  /\ AScheduler LB m schedb (mkSCH (mkSVC AVP_SCHED AL_TYPEID_SCHED 0 ioc cfgb P_A_DESTROY_ALLOC_SCHED) 0 0 0)
  /\ AStreamSvc LB m ssvcb (mkSVC AVP_SSVC 0 AG_ID_SSVC ioc schedb P_A_DESTROY_ALLOC_SSVC) implb
  /\ AImplBlockV LB m implb 1 1 [] 1.

(* [comment removed for export] *)
Lemma AErrCode_clear_intro : forall m a, rw_cells bsegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> AErrCode m a EC_clear.
Proof. intros m a H. split; [exact H|]. unfold ec_ok, EC_clear; cbn; lia. Qed.
Lemma AFlatBuf_empty_intro : forall LB m a,
  rw_cells bsegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz u64max)] -> AFlatBuf LB m a FB_empty [].
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
     rw_cells bsegs m AVP_ALLOCIMPL   (wcells [AVS_ALLOCIMPL_0; AVS_ALLOCIMPL_8; AVS_ALLOCIMPL_16; AVS_ALLOCIMPL_24; AVS_ALLOCIMPL_32])
  /\ rw_cells bsegs m AVP_CONFIG_SVC  (wcells [AVS_CONFIG_SVC_0; AVS_CONFIG_SVC_8; AVS_CONFIG_SVC_16; AVS_CONFIG_SVC_24; AVS_CONFIG_SVC_32])
  /\ rw_cells bsegs m AVP_SCHED       (wcells [AVS_SCHED_0; AVS_SCHED_8; AVS_SCHED_16; AVS_SCHED_24])
  /\ rw_cells bsegs m AVP_SSVC        (wcells [AVS_SSVC_0; AVS_SSVC_8; AVS_SSVC_16; AVS_SSVC_24])
  /\ rw_cells bsegs m AVP_SPCI_IMPL   (wcells [AVS_SPCI_IMPL_0; AVS_SPCI_IMPL_8; AVS_SPCI_IMPL_16; AVS_SPCI_IMPL_24; AVS_SPCI_IMPL_32; AVS_SPCI_IMPL_40; AVS_SPCI_IMPL_48])
  /\ rw_cells bsegs m AVP_SPCI_STATE  (wcells [AVS_SPCI_STATE_0; AVS_SPCI_STATE_8; AVS_SPCI_STATE_16; AVS_SPCI_STATE_24; AVS_SPCI_STATE_32; AVS_SPCI_STATE_40; AVS_SPCI_STATE_48])
  /\ rw_cells bsegs m AVP_PARSER      (wcells [AVS_PARSER_0; AVS_PARSER_8; AVS_PARSER_16; AVS_PARSER_24; AVS_PARSER_32; AVS_PARSER_40; AVS_PARSER_48; AVS_PARSER_56; AVS_PARSER_64; AVS_PARSER_72; AVS_PARSER_80; AVS_PARSER_88])
  /\ rw_cells bsegs m AVP_HTTP_ECAT   (wcells [AVS_HTTP_ECAT_0; AVS_HTTP_ECAT_8; AVS_HTTP_ECAT_16; AVS_HTTP_ECAT_24; AVS_HTTP_ECAT_32; AVS_HTTP_ECAT_40; AVS_HTTP_ECAT_48])
  /\ rw_cells bsegs m AT_ANYEX_OBJECT_FNS (wcells AT_ANYEX_OBJECT_FNS_words)
  /\ rw_cells bsegs m AT_ANYEX_TARGET_FNS (wcells AT_ANYEX_TARGET_FNS_words)
  /\ rw_cells bsegs m AT_ANYEX_PROP_FNS   (wcells AT_ANYEX_PROP_FNS_words)
  /\ rw_cells bsegs m AT_ANYEX_PROP_FNS_VOID (wcells AT_ANYEX_PROP_FNS_VOID_words)
  /\ rw_cells bsegs m (AL_TYPEID_CONFIG + 8) (wcells [ATI_NAME_CONFIG])
  /\ rw_cells bsegs m (AL_TYPEID_SCHED + 8)  (wcells [ATI_NAME_SCHED])
  /\ rw_cells bsegs m AG_SYSTEM_CAT_INST (wcells [AW_SYSTEM_CAT_VPTR; W_SYSTEM_CAT_ID])
  /\ rw_cells bsegs m AG_MISC_CAT_INST   (wcells [AW_MISC_CAT_VPTR; W_MISC_CAT_ID]).

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
  AXStatics2 m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0x12a180 <= fst iv \/ snd iv <= 0x119000) W ->
  AXStatics2 m'.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.XS.AXStatics2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@Corelib.Lists.ListDef.Forall); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.or); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.fst); constr:(@Corelib.Init.Datatypes.snd); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Init.Datatypes.list_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Logic.I); constr:(@kc__1); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.pair); constr:(@Stdlib.Lists.List.Forall_inv); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.Lists.List.Forall_inv_tail); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVP_ALLOCIMPL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.wcells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_ALLOCIMPL_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_ALLOCIMPL_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_ALLOCIMPL_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_ALLOCIMPL_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_ALLOCIMPL_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVP_CONFIG_SVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_CONFIG_SVC_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_CONFIG_SVC_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_CONFIG_SVC_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_CONFIG_SVC_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_CONFIG_SVC_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVP_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SCHED_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SCHED_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SCHED_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SCHED_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVP_SSVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SSVC_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SSVC_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SSVC_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SSVC_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVP_SPCI_IMPL); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_IMPL_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_IMPL_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_IMPL_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_IMPL_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_IMPL_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_IMPL_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_IMPL_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVP_SPCI_STATE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_STATE_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_STATE_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_STATE_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_STATE_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_STATE_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_STATE_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_SPCI_STATE_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVP_PARSER); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_56); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_64); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_72); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_80); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVS_PARSER_88); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AVP_HTTP_ECAT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AVS_HTTP_ECAT_0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AVS_HTTP_ECAT_8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AVS_HTTP_ECAT_16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AVS_HTTP_ECAT_24); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AVS_HTTP_ECAT_32); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AVS_HTTP_ECAT_40); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AVS_HTTP_ECAT_48); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_OBJECT_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_OBJECT_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_TARGET_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_TARGET_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_PROP_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_PROP_FNS_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_PROP_FNS_VOID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_PROP_FNS_VOID_words); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AL_TYPEID_CONFIG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.ATI_NAME_CONFIG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AL_TYPEID_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.ATI_NAME_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AG_SYSTEM_CAT_INST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AW_SYSTEM_CAT_VPTR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.W_SYSTEM_CAT_ID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AG_MISC_CAT_INST); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AW_MISC_CAT_VPTR); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.W_MISC_CAT_ID); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.and_morph); constr:(@Stdlib.micromega.ZifyClasses.eq_iff); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@kc__1 (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))|] [|@iv; @FW; @W; @l; @p; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__arith; @H1; @IH; @hi; @lo; @z; @a; @HA; @n; @A; @x; @y; @m; @H14; @H13; @H12; @H11; @H10; @H9; @H8; @H7; @H6; @H5; @H4; @H3; @H2; @H0; @H; @D; @WM; @MU; @XS; @m'|] "#?W#g%Q#u#x$<$=##$;%@%C%:%8%6$B$D%4%,${#$$$#z$s#a#d$k$f$a$[$T#-#)#,#.#b#*#1#5#9#=#A#E#I#M#Q#U#Y#]#g#f#e#%#0%G#4#&#2#8#6#<#:#@#>#D#B#H#k#(#F#L%R#'#J#P#N#T#R#X$.#V#\#p#Z#j#n#m#r#+$3$/$4$6$5$>$9$K$L#/#^#_#`#q#s#t#w#}#~$($,$7$8$:$E$H$N$M$O$P$I$Q$)$%$Z$Y$X$W$V$`$_$^$]$\$e$d$c$b$j$i$h$g$r$q$p$o$n$m$l$z$y$x$w$v$u$t%+%*%)%(%'%&%%%$%#$~$}$|%3%2%1%0%/%.%-%5%7%9%;%<%=%>%?%B%A%E%D#3#7#;#?#C#G#K#O#S#W#[#c%M%O%P#l$#$S$2#o#|$*$J$@$?#{$A$G$F$-$U%H%K%N%L%J%I%F$R$&%Q#v$1#y$0$C$'$+G%1%%2'%3$%4$#5%#4%%5$%6&%7%%8'%9*%:$%;%#U$%<&%=*%>'%?$%@$%A&%B5%C/%D)%E'$'&%F-%G(%H&%I/%J&%K%%L%%M&%N%%O$%P'UScSR&Sa&#&#&#&#&#USd#USe#USd(USe#USu#k##&#USfS#WSvSGSCS#WSwCSGSCVSxDD)1&#)#&#)#&#&#&#)#)#&#)#&#&#&#&#&#&#.#WSyDDG&Sa&#)#&#)#&#)#&#&#&#&#)#)#&#&#&#&#&#&#&#.#&6)#)#&#&#)#&#&#&#&#&#&#&#&#&#&#&#&#.#)2&#&#&#)#)#&#&#&#&#)#&#&#&#.#)?)#)#)#)#&#)#&#)#&#&#&#.#)<)#&#)#)#)#&#&#&#&#&#.#)s#*&#)#)#&#&#)#)#&#&#&#&#&#.#),)#&#&#&#&#&#&#.#)6&#&#)#)#&#&#&#&#.#)s#.)#)#&#&#)#&#&#&#.#)s#T&#&#&#)#)#)#)#)#&#&#&#.#)s#:&#&#&#)#)#)#&#&#&#&#&#.#&,&#)#&#)#&#&#&#.#)6&#&#&#&#&#&#&#&#.#)s#C&#&#&#&#&#&#&#.#&s$,&#&#)#)#)#)#&#&#&#.#&s#x&#&#&#&#&#&#&#.#&s$h&#)#)#)#)#&#)#&#&#)#)#&#&#&#&#.#),)#&#)#)#&#&#&#.#'s$qs%*WSzDDG)s%M)#&#&#)#&#&#&#&#&#&#&#&#&#&#&#&#.#'5s$rB7#j#$s%T#@s%U#SS's$vS#(S#G'#s%/#%#@s%Z(G>S#SWSGk#%$#j#&s%m#ESR@s%_-#j#%#S{>S#S/SSk#%*#*SRSCS#@s%d2#*SRSGSC>#S3S/k#%%#k##(#k#'s%y#j#(s%j#>S#S0Sgk#%4#FDDSGSC*SR#S#@s%o=#FDDSWSGYS|s%q?#SCGU@$(S1S.'#SS'SWS1B$#>SGS1S.%Sh%#%#%#AD#AD%ADShCD$#CD&#VSi#SjAD+AD-CD$#CD+#VSi#SjES^*S^$#*S^*#UScS^VSkDSWUS}DXSlD$SC#VSkDSGXSlD$S##US~DUT#D/Ds%i)SaDD#,D%N#-'HEEF#ODDs&I/Ds%\,D$N#-+HEEF#O[Sm,HEEF'#UT$EDDSa,D(N#-0HEEF#ODDs&S1D&#,D#N2-4HEEF#O25HEEF'#,D&N3-7HEEF#O,D2N,-9HEEF#O[Sm:HEEF%#\Sn;HEEF(0#\Sn<HEEF21#VT%=F+SoSpVT&GSCWT'So#Spm$%#WT(DT)S#XT*GSC$#l#)*)#l#*s#'s#&#l#+s#.s#-#j#,D#j#-D#j#.D#j#/D#'s&5SC'SGs&#B$#(S#SC'#s&9#s#k#(SCSG'#SW'SSSCB$#k##'#k##+#k#,D#k#-D#k#.D#k#/D#ZGSSS/S1SqS#S.l#04$#FDDSSSWYT+s&qs#{#SGS#USC#3s#[s#Z&#*SR&SG>#S1S.m#%#l#1s#ds#c#j#%s#g#j#2s#k#j#&s'.#j#3D#j#4D#V#S#Gj#5D#j#5D#YT,DDs#t#Gj#6SR#ZT-SRs$'s$$#S0SGj#7s$,#j#8D#j#9D#>S0SCS#k##s$0#k#8D#k#9D#ED*DT.#*DT/#*DT0#*DT1#*DT2#4#$CS/S-#*DT3**DT4#*DT5#*DT6#*DT7#4#$CS/S,#*DT81*DT9#*DT:#*DT;#4#$CS/S+#*DT<7*DT=#*DT>#*DT?#4#$CS/S*#*DT@=*DTA#*DTB#*DTC#*DTD#*DTE#*DTF#4#$CS/S)#*DTGs#&*DTH#*DTI#*DTJ#*DTK#*DTL#*DTM#4#$CS/S&#*DTNs#/*DTO#*DTP#*DTQ#*DTR#*DTS#*DTT#*DTU#*DTV#*DTW#*DTX#*DTY#4#$CS/R#*DTZs#=*DT[#*DT\#*DT]#*DT^#*DT_#*DT`#4#$CS/Q#4Ta$CS/P#4Tb$CS/M#4Tc$CS/L#4Td$CS/K#.s(+(Te#*DTfs#P4#$CS/%#(Tg'*DThs#T4#$CS/%#*DTis#W*DTj#4#$CS/I#*DTks#[*DTl#4#$CS/J##'##,##1##7##:##=##@##s####s#-##s#<##s#F##s#P##s#W##s#^##s#f#j####$CS3S,s#b$CS3S+s#]$CS3S*s#X$CS3S)s#P$CS3S&s#H$CS3Rs#;$CS3Qs#3$CS3Ps#2$CS3Ms#1$CS3Ls#0$CS3Ks#/$CS3s#-s#+$CS3s#*s#($CS3Is#%$CS3JB#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CSgS-s$*$CS0S,s$$$CS0S+s#{$CS0S*s#v$CS0S)s#n$CS0S&s#f$CS0Rs#Y$CS0Qs#Q$CS0Ps#P$CS0Ms#O$CS0Ls#N$CS0Ks#M$CS0s#Ks#I$CS0s#Hs#F$CS0Is#C$CS0Js#@#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CS.S,s$A$CS.S+s$<$CS.S*s$7$CS.S)s$/$CS.S&s$'$CS.Rs#v$CS.Qs#n$CS.Ps#m$CS.Ms#l$CS.Ls#k$CS.Ks#j$CS.s#hs#f$CS.s#es#c$CS.Is#`$CS.Js#]#$##&##(##*##,##.##0##2##4##6##8##:##<##>#$CS.S-s$e##$j##%#$CS1S+s$[$CS1S*s$V$CS1S)s$N$CS1S&s$F$CS1Rs$9$CS1Qs$1$CS1Ps$0$CS1Ms$/$CS1Ls$.$CS1Ks$-$CS1s$+s$)$CS1s$(s$&$CS1Is$#$CS1Js#|#$##&##(##*##,##.##0##2##4##6##8##:##<#$CSqS,s$|$CSDS+s$w$CSDS*s$r$CSDS)s$j$CSDS&s$b$CSDRs$U$CSDQs$M$CSDPs$L$CSDMs$K$CSDLs$J$CSDKs$I$CSDs$Gs$E$CSDs$Ds$B$CSDIs$?$CSDJs$<#$##&##(##*##,##.##0##2##4##6##8##:##<#$CS4S+s%6$CS4S*s%1$CS4S)s%)$CS4S&s$}$CS4Rs$p$CS4Qs$h$CS4Ps$g$CS4Ms$f$CS4Ls$e$CS4Ks$d$CS4s$bs$`$CS4s$_s$]$CS4Is$Z$CS4Js$W#$##&##(##*##,##.##0##2##4##6##8##:##<#$CS4S-s%^$CS4S,s%X##%#%#j##'#$CSHS*s%P$CSHS)s%H$CSHS&s%@$CSHRs%3$CSHQs%+$CSHPs%*$CSHMs%)$CSHLs%($CSHKs%'$CSHs%%s%#$CSHs$~s$|$CSHIs$y$CSHJs$v#$##&##(##*##,##.##0##2##4##6##8##:#$CTmS+s%o$CSFS*s%j$CSFS)s%b$CSFS&s%Z$CSFRs%M$CSFQs%E$CSFPs%D$CSFMs%C$CSFLs%B$CSFKs%A$CSFs%?s%=$CSFs%<s%:$CSFIs%7$CSFJs%4#$##&##(##*##,##.##0##2##4##6##8##:#$CS5S*s&'$CS5S)s%{$CS5S&s%s$CS5Rs%f$CS5Qs%^$CS5Ps%]$CS5Ms%\$CS5Ls%[$CS5Ks%Z$CS5s%Xs%V$CS5s%Us%S$CS5Is%P$CS5Js%M#$##&##(##*##,##.##0##2##4##6##8##:#$CS5S-s&S$CS5S,s&M$CS5S+s&H##&#%##'#j##)#$CSJS)s&>$CSJS&s&6$CSJRs&)$CSJQs%}$CSJPs%|$CSJMs%{$CSJLs%z$CSJKs%y$CSJs%ws%u$CSJs%ts%r$CSJIs%o$CSJJs%l#$##&##(##*##,##.##0##2##4##6##8#$CTnS*s&^$CSIS)s&V$CSIS&s&N$CSIRs&A$CSIQs&9$CSIPs&8$CSIMs&7$CSILs&6$CSIKs&5$CSIs&3s&1$CSIs&0s&.$CSIIs&+$CSIJs&(#$##&##(##*##,##.##0##2##4##6##8#$CS6S)s&m$CS6S&s&e$CS6Rs&X$CS6Qs&P$CS6Ps&O$CS6Ms&N$CS6Ls&M$CS6Ks&L$CS6s&Js&H$CS6s&Gs&E$CS6Is&B$CS6Js&?#$##&##(##*##,##.##0##2##4##6##8#$CS6S-s'D$CS6S,s'>$CS6S+s'9$CS6S*s'4##'#%##'##)#j##+#$CSLS&s'($CSLRs&w$CSLQs&o$CSLPs&n$CSLMs&m$CSLLs&l$CSLKs&k$CSLs&is&g$CSLs&fs&d$CSLIs&a$CSLJs&^#$##&##(##*##,##.##0##2##4##6#$CToS)s'F$CSKS&s'>$CSKRs'1$CSKQs')$CSKPs'($CSKMs''$CSKLs'&$CSKKs'%$CSKs'#s&}$CSKs&|s&z$CSKIs&w$CSKJs&t#$##&##(##*##,##.##0##2##4##6#$CS7S&s'S$CS7Rs'F$CS7Qs'>$CS7Ps'=$CS7Ms'<$CS7Ls';$CS7Ks':$CS7s'8s'6$CS7s'5s'3$CS7Is'0$CS7Js'-#$##&##(##*##,##.##0##2##4##6#$CS7S-s(1$CS7S,s(+$CS7S+s(&$CS7S*s'}$CS7S)s'u##(#%##'##)##+#j##-#$CSNRs'e$CSNQs']$CSNPs'\$CSNMs'[$CSNLs'Z$CSNKs'Y$CSNs'Ws'U$CSNs'Ts'R$CSNIs'O$CSNJs'L#$##&##(##*##,##.##0##2##4#$CTpS&s(*$CSMRs'y$CSMQs'q$CSMPs'p$CSMMs'o$CSMLs'n$CSMKs'm$CSMs'ks'i$CSMs'hs'f$CSMIs'c$CSMJs'`#$##&##(##*##,##.##0##2##4#$CS8Rs(0$CS8Qs(($CS8Ps('$CS8Ms(&$CS8Ls(%$CS8Ks($$CS8s'~s'|$CS8s'{s'y$CS8Is'v$CS8Js's#$##&##(##*##,##.##0##2##4#$CS8S-s(v$CS8S,s(p$CS8S+s(k$CS8S*s(f$CS8S)s(^$CS8S&s(V##)#%##'##)##+##-#j##/#$CSPQs(G$CSPPs(F$CSPMs(E$CSPLs(D$CSPKs(C$CSPs(As(?$CSPs(>s(<$CSPIs(9$CSPJs(6#$##&##(##*##,##.##0##2#$CTqRs(a$CSOQs(Y$CSOPs(X$CSOMs(W$CSOLs(V$CSOKs(U$CSOs(Ss(Q$CSOs(Ps(N$CSOIs(K$CSOJs(H#$##&##(##*##,##.##0##2#$CS9Qs(j$CS9Ps(i$CS9Ms(h$CS9Ls(g$CS9Ks(f$CS9s(ds(b$CS9s(as(_$CS9Is(\$CS9Js(Y#$##&##(##*##,##.##0##2#$CS9S-s)[$CS9S,s)U$CS9S+s)P$CS9S*s)K$CS9S)s)C$CS9S&s);$CS9Rs).##*#%##'##)##+##-##/#j##1#$CSTPs),$CSTMs)+$CSTLs)*$CSTKs))$CSTs)'s)%$CSTs)$s(~$CSTIs({$CSTJs(x#$##&##(##*##,##.##0#$CTrQs)=$CSQPs)<$CSQMs);$CSQLs):$CSQKs)9$CSQs)7s)5$CSQs)4s)2$CSQIs)/$CSQJs),#$##&##(##*##,##.##0#$CS:Ps)K$CS:Ms)J$CS:Ls)I$CS:Ks)H$CS:s)Fs)D$CS:s)Cs)A$CS:Is)>$CS:Js);#$##&##(##*##,##.##0#$CS:S-s*<$CS:S,s*6$CS:S+s*1$CS:S*s*,$CS:S)s*$$CS:S&s)x$CS:Rs)k$CS:Qs)c##+#%##'##)##+##-##/##1#j##3#$CSXMs)i$CSXLs)h$CSXKs)g$CSXs)es)c$CSXs)bs)`$CSXIs)]$CSXJs)Z#$##&##(##*##,##.#$CTsPs)x$CSUMs)w$CSULs)v$CSUKs)u$CSUs)ss)q$CSUs)ps)n$CSUIs)k$CSUJs)h#$##&##(##*##,##.#$CS;Ms*($CS;Ls*'$CS;Ks*&$CS;s*$s)~$CS;s)}s){$CS;Is)x$CS;Js)u#$##&##(##*##,##.#$CS;S-s*u$CS;S,s*o$CS;S+s*j$CS;S*s*e$CS;S)s*]$CS;S&s*U$CS;Rs*H$CS;Qs*@$CS;Ps*?##,#%##'##)##+##-##/##1##3#j##5#$CSZLs*F$CSZKs*E$CSZs*Cs*A$CSZs*@s*>$CSZIs*;$CSZJs*8#$##&##(##*##,#$CTtMs*S$CSYLs*R$CSYKs*Q$CSYs*Os*M$CSYs*Ls*J$CSYIs*G$CSYJs*D#$##&##(##*##,#$CS<Ls*]$CS<Ks*\$CS<s*Zs*X$CS<s*Ws*U$CS<Is*R$CS<Js*O#$##&##(##*##,#$CS<S-s+N$CS<S,s+H$CS<S+s+C$CS<S*s+>$CS<S)s+6$CS<S&s+.$CS<Rs*}$CS<Qs*u$CS<Ps*t$CS<Ms*s##-#%##'##)##+##-##/##1##3##5#j##7#$CS\Ks*{$CS\s*ys*w$CS\s*vs*t$CS\Is*q$CS\Js*n#$##&##(##*#$CTuLs+*$CS[Ks+)$CS[s+'s+%$CS[s+$s*~$CS[Is*{$CS[Js*x#$##&##(##*#$CS=Ks+2$CS=s+0s+.$CS=s+-s++$CS=Is+($CS=Js+%#$##&##(##*#$CS=S-s,#$CS=S,s+y$CS=S+s+t$CS=S*s+o$CS=S)s+g$CS=S&s+_$CS=Rs+R$CS=Qs+J$CS=Ps+I$CS=Ms+H$CS=Ls+G##.#%##'##)##+##-##/##1##3##5##7#j##9#$CS_s+Os+M$CS_s+Ls+J$CS_Is+G$CS_Js+D#$##&##(#$CTvKs+Y$CS]s+Ws+U$CS]s+Ts+R$CS]Is+O$CS]Js+L#$##&##(#$CS>s+^s+\$CS>s+[s+Y$CS>Is+V$CS>Js+S#$##&##(#$CS>S-s,P$CS>S,s,J$CS>S+s,E$CS>S*s,@$CS>S)s,8$CS>S&s,0$CS>Rs,#$CS>Qs+w$CS>Ps+v$CS>Ms+u$CS>Ls+t$CS>Ks+s##/#%##'##)##+##-##/##1##3##5##7##9#j##;#$CSbs+zs+x$CSbIs+u$CSbJs+r#$##&#$CTws,'s,%$CS`s,$s+~$CS`Is+{$CS`Js+x#$##&#$CS?s,)s,'$CS?Is,$$CS?Js+}#$##&#$CS?S-s,y$CS?S,s,s$CS?S+s,n$CS?S*s,i$CS?S)s,a$CS?S&s,Y$CS?Rs,L$CS?Qs,D$CS?Ps,C$CS?Ms,B$CS?Ls,A$CS?Ks,@$CS?s,>s,<##0#%##'##)##+##-##/##1##3##5##7##9##;#j##=#$CSrIs,C$CSrJs,@#$#$CSss,Ls,J$CStIs,G$CStJs,D#$#$CS'Is,J$CS'Js,G#$#$CS'S-s-B$CS'S,s-<$CS'S+s-7$CS'S*s-2$CS'S)s-*$CS'S&s,~$CS'Rs,q$CS'Qs,i$CS'Ps,h$CS'Ms,g$CS'Ls,f$CS'Ks,e$CS's,cs,a$CS's,`s,^##1#%##'##)##+##-##/##1##3##5##7##9##;##=#j##?#$CS2Js,f$CTxIs,k$CS(Js,h$CS(S-s-b$CS(S,s-\$CS(S+s-W$CS(S*s-R$CS(S)s-J$CS(S&s-B$CS(Rs-5$CS(Qs--$CS(Ps-,$CS(Ms-+$CS(Ls-*$CS(Ks-)$CS(s-'s-%$CS(s-$s,~$CS(Is,{##2#%##'##)##+##-##/##1##3##5##7##9##;##=#5s.#0#)s/s&#&#)#&#&#)#&#)#&#)#&#&#&#.#'s2*s1w%s/J%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#(s2A#'#s2d#s#*#)s3B&#&#&#.#(s2I#'#s2l#s#2#+S@s#36s#4s#4#j#:DG'S#GUTy#j#;D#j#:D#XTzDDT{s0I+D#j#<D#j#8D#+Ds2W0G+D#j#:SV#+D5?SVDDDSESE00$?6#7DDDDDDS$111S$)s2]s2](?7#+Ds3$8DDS%3S%/@8$s3%s3%#9s#G@s#G85#/Ds2a,Ds/sN#-s/{HEEF#O/D>1D&#,D#Ns/}-s0#HEEF#O2s0$HEEF'#l#)#s/fs/`l#*s0+s0'#l#+s01s0.#l#0#s##G:s#,s#$/#m##s#-'s2~S-(S-s#2'#s37#%#m#'#(S-s#k'#s3;#)#m#&#;S-s#o#<CSASBS(S-s/6S`S2S'#5s/00#&s#p&#)#&#)#&#&#)#&#&#&#.#'s3;s2{(s2|s#K'#s3P#%#(s3#s#F'#s3S#(#+S@)6**#+Ds3(7DDDDDDS$s#Fs#Fs#FS$s#>s3)s3)#s#Ts#Ls#88DDS%s#GS%s#C,)#s3Ys3Ys#79.,.)&#/Ds3,,Ds0KN#-s0SHEEF#O1D%s#6,D#Ns0T-s0VHEEF#O2s0WHEEF&#l#)#s0=s07l#*s0^s0Z#l#+s0ds0a#l#0#3G:74.#m##8's3US,(S,s#e'#s3j#%#m#'#(S,s#.'#s3n#)#m#&#;S,s#2#<CSASBS(S,s/bS]S2S'#5s/]0#)s$H&#&#&#)#&#&#&#&#&#&#&#.#'s3os3G0s$,(s3I#'#s4)#&#.s4_(s3M#'#s4-#*#+S@+6,,#+Ds3R+D)?SVDDDSESEs#}s#}s#qs$8*#7DDDDDDS$s#~s#~s#~S$s#vs3Us3U%/+#8DDS%s$#S%s#{/+#s45s45s#o92/2+(#/Ds3X,Ds1'N#-s1/HEEF#O/D11D&#,D#Ns11-s13HEEF#O2s14HEEF'#l#)#s0vs0pl#*s1;s17#l#+s1As1>#l#0#6G:;7/#m##<'s42S+(S+A'#s4G#%#m#'#(S+s#4'#s4K#)#m#&#;S+s#8#<CSASBS(S+s09S[S2S'#5s040#)s%&)#&#&#&#&#&#&#&#&#&#&#&#.#'s4Ms3s(s3ts#<'#s4b#%#(s3ws#;'#s4e#(#+S@)6**#+Ds3|7DDDDDDS$s$Xs$Xs$XS$s$Ps3}s3}#s#Es#As#98DDS%s$YS%s$U,)#s4ks4ks$I9.,.)&#/Ds4$,Ds1]N#-s1eHEEF#O1D%s#8,D#Ns1f-s1hHEEF#O2s1iHEEF&#l#)#s1Os1Il#*s1ps1l#l#+s1vs1s#l#0#3G:74.#m##8's4gS*(S*s#V'#s4|#%#m#'#(S*s#0'#s5$#)#m#&#;S*s#4#<CSASBS(S*s0hSYS2S'#5s0`0#)s#2)#&#&#&#&#&#.#'s4|s4=%s%1%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#(s4O#'#s5F#6#)s2<&#&#&#.#(s4W#'#s5N#>#+S@?6@@#+Ds4\+D)?SVDDDSESEs%Bs%Bs%63*#7DDDDDDS$s%Cs%Cs%CS$s%;s4_s4_%3+#8DDS%s%DS%s%@3+#s5Vs5Vs%49s#&3s#&+(#/Ds4b,Ds2HN#-s2PHEEF#O/D11D&#,D#Ns2R-s2THEEF#O2s2UHEEF'#l#)#s2;s25l#*s2\s2X#l#+s2bs2_#l#0#6G:?7/#m##@'s5SS)(S)s#%'#s5h#%#m#'#(S)s#C'#s5l#)#m#&#;S)s#G#<CSASBS(S)s1KSUS2S'#5s1C0#)s#{)#&#)#&#&#&#&#.#'s5is4|(s4}s#;'#s5~#%#(s5$s#6'#s6%#(#+S@)6**#+Ds5)7DDDDDDS$s%ts%ts%tS$s%ls5*s5*#s#Ds#<s#48DDS%s%uS%s%q,)#s6+s6+s%e9.,.)&#/Ds5-,Ds2yN#-s3%HEEF#O1D%s#3,D#Ns3&-s3(HEEF#O2s3)HEEF&#l#)#s2ks2el#*s30s3,#l#+s36s33#l#0#3G:74.#m##8's6'S&(S&s#U'#s6<#%#m#'#(S&s#+'#s6@#)#m#&#;S&s#/#<CSASBS(S&s1rSQS2S'#5s1e0#)s%.&#)#)#&#)#&#&#&#.#'s6>s5G%s#m%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#(s5q#'#s6|#s#.#&s3r&#&#&#&#.#(s5z#'#s7)#s#7#+S@s#86s#9s#9#+Ds6#+D)?SVDDDSESEs&ys&ys&m4*#7DDDDDDS$s&zs&zs&zS$s&rs6&s6&%4+#8DDS%s&{S%s&w4+#s71s71s&k9s#?4s#?+(#/Ds6),Ds4#N#-s4+HEEF#O/D11D&#,D#Ns4--s4/HEEF#O2s40HEEF'#l#)#s3rs3ll#*s47s43#l#+s4=s4:#l#0#6G:@7/#m##A's7.R(Rs#&'#s7C#%#m#'#(Rs#^'#s7G#)#m#&#;Rs#b#<CSASBS(Rs2kSOS2S'#5s2c0#)s&6&#)#&#&#)#)#&#&#&#.#'s7Fs6B(s6Cs$t'#s7[#%#(s6Fs$o'#s7^#(#+S@)6**#+Ds6K7DDDDDDS$s'Qs'Qs'QS$s'Is6Ls6L#s$}s$us$m8DDS%s'RS%s'N,)#s7ds7ds'B9.,.)&#/Ds6O,Ds4VN#-s4^HEEF#O1D%s$l,D#Ns4_-s4aHEEF#O2s4bHEEF&#l#)#s4Hs4Bl#*s4is4e#l#+s4os4l#l#0#3G:74.#m##8's7`Q(Qs%2'#s7u#%#m#'#(Qs#-'#s7y#)#m#&#;Qs#1#<CSASBS(Qs38SMS2S'#5s370#)s&.&#)#&#&#&#&#&#&#&#.#'s7xs6g(s6hs&g'#s81#%#(s6ks&f'#s84#(#+S@)6**#+Ds6p7DDDDDDS$s('s('s('S$s'{s6qs6q#s&ps&ls&d8DDS%s((S%s($,)#s8:s8:s't9.,.)&#/Ds6t,Ds5,N#-s54HEEF#O1D%s&c,D#Ns55-s57HEEF#O2s58HEEF&#l#)#s4zs4tl#*s5?s5;#l#+s5Es5B#l#0#3G:74.#m##8's86P(Ps'%'#s8K#%#m#'#(Ps#-'#s8O#)#m#&#;Ps#1#<CSASBS(Ps3hSKS2S'#5s3g0#)s&_)#)#&#&#)#&#&#&#.#'s8Ms73(s74s'<'#s8b#%#(s77s';'#s8e#(#+S@)6**#+Ds7<7DDDDDDS$s(Xs(Xs(XS$s(Ps7=s7=#s'Es'As'98DDS%s(YS%s(U,)#s8ks8ks(I9.,.)&#/Ds7@,Ds5]N#-s5eHEEF#O1D%s'8,D#Ns5f-s5hHEEF#O2s5iHEEF&#l#)#s5Os5Il#*s5ps5l#l#+s5vs5s#l#0#3G:74.#m##8's8gM(Ms'V'#s8|#%#m#'#(Ms#,'#s9$#)#m#&#;Ms#0#<CSASBS(Ms4;SIS2S'#5s4:0#)s#b&#&#&#&#&#.#'s8{s7W%s$t%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#%#0#(s8E#'#s9}#s#N#)s)v&#&#&#.#(s8M#'#s:)#s#V#+S@s#W6s#Xs#X#+Ds8R+D)?SVDDDSESEs)ys)ys)m3*#7DDDDDDS$s)zs)zs)zS$s)rs8Us8U%3+#8DDS%s){S%s)w3+#s:1s:1s)k9s#^3s#^+(#/Ds8X,Ds7#N#-s7+HEEF#O/D11D&#,D#Ns7--s7/HEEF#O2s70HEEF'#l#)#s6rs6ll#*s77s73#l#+s7=s7:#l#0#6G:?7/#m##@'s:.L(Ls#%'#s:C#%#m#'#(Ls#z'#s:G#)#m#&#;Ls#~#<CSASBS(Ls5\SFS2S'#5s5[0#&s$V&#)#&#&#&#&#&#.#'s:Ds8s(s8ts#;'#s:Y#%#(s8ws#6'#s:\#(#+S@)6**#+Ds8|7DDDDDDS$s*Os*Os*OS$s*Gs8}s8}#s#Ds#<s#48DDS%s*PS%s*L,)#s:bs:bs*@9.,.)&#/Ds9$,Ds7TN#-s7\HEEF#O1D%s#3,D#Ns7]-s7_HEEF#O2s7`HEEF&#l#)#s7Fs7@l#*s7gs7c#l#+s7ms7j#l#0#3G:74.#m##8's:^K(Ks#U'#s:s#%#m#'#(Ks#+'#s:w#)#m#&#;Ks#/#<CSASBS(Ks6.SDS2S'#5s6*0#)s*>&#&#&#&#)#)#&#&#&#.#(s9>s6:'s:w#0s+L(%#'#s;1#&#((s6@'#s;4#)#+S@*6++#+D-+Ds6F?SVDDDSESEs+(s+(s*xs+Ws6G#7DDDDDDS$s+)s+)s+)S$s*}00%.s6H#8DDS%s+*S%s+&.+#s;<s;<s*v91.1+(#/Ds9O/Ds6L1D$#,Ds80N#-s88HEEF#O1D%&,D#Ns89-s8;HEEF#O2s8<HEEF&#l#)#s7~s7xl#*s8Cs8?#l#+s8Is8F#l#0#7G:;80#m##<'s;:s6Y(s6ZA'#s;O#%#m#'#(s6^s#3'#s;S#)#m#&#;s6bs#7#<CSASBS(s6cs6aS0S2S'#5s6^0#)s,+)#)#&#)#&#&#&#&#&#.#(s9ms6r's;S#($s#:'#s;h#%#('s6w'#s;k#(#+S@)6**#+D,7DDDDDDS$s+^s+^s+^S$s+V--#s#Cs6}s#88DDS%s+_S%s+[,)#s;qs;qs+O9.,.)&#/Ds9{1D#s#7,Ds8dN#-s8lHEEF#O1D%s#:,D#Ns8m-s8oHEEF#O2s8pHEEF&#l#)#s8Vs8Pl#*s8ws8s#l#+s8}s8z#l#0#4G:85/#m##9's;ns7-(s7.s#U'#s<'#%#m#'#(s72s#/'#s<+#)#m#&#;s76s#3#<CSASBS(s77s75SSS2S'#5s720#&s<Y&#)#)#)#)#)#&#)#)#&#)#&#&#&#&#.#'s<0s::0s,Y(s:<#'#s<F#&#.s<}(s:@#'#s<J#*#+S@+6,,#+Ds:E+D)?SVDDDSESEs,>s,>s,2s,e*#7DDDDDDS$s,?s,?s,?S$s,7s:Hs:H%/+#8DDS%s,@S%s,</+#s<Rs<Rs,092/2+(#/Ds:K,Ds9DN#-s9LHEEF#O/D11D&#,D#Ns9N-s9PHEEF#O2s9QHEEF'#l#)#s97s91l#*s9Xs9T#l#+s9^s9[#l#0#6G:;7/#m##<'s<OI(IA'#s<d#%#m#'#(Is#8'#s<h#)#m#&#;Is#<#<CSASBS(Is7nS#S2S'#5s7k0#)s#9&#)#)#)#)#&#&#&#.#'s<fs:g(s:hs#8'#s<{#%#(s:ks#7'#s<~#(#+S@)6**#+Ds:p7DDDDDDS$s,qs,qs,qS$s,is:qs:q#s#As#=s#58DDS%s,rS%s,n,)#s=(s=(s,b9.,.)&#/Ds:t,Ds9vN#-s9~HEEF#O1D%s#4,D#Ns:#-s:%HEEF#O2s:&HEEF&#l#)#s9hs9bl#*s:-s:)#l#+s:3s:0#l#0#3G:74.#m##8's=$J(Js#R'#s=9#%#m#'#(Js#,'#s==#)#m#&#;Js#0#<CSASBS(Js8?GS2S'#3s.'s.6s#4#3s.)s.'s#r#3s.+s.'s$K#3s.-s.'s%(#3s./s.'s%Y#3s.1s.'s&}#3s.3s.'s'S#3s.5s.'s(*#3s.7s.'s(]#3s.9s.'s)e#3s.;s.'s*:#3s.=s.'s+'#3s.?s.'s+]#3s.As.'s,;#3s.Cs.'s,o#j#=s.E#j#>s.G#V#S#Gj##s.J#j##s.k#=s.ls.ks.M#Gj#>s.n#j#?s.r#V#S#Gj##s.u#j##s/<#=s/=s/:s.z#Gj#?s/?#j#@s/E#V#S#Gj##s/H#j##s/m#=s/ns/is/O#Gj#@s/p#j#As/x#V#S#Gj##s/{#j##s0F#=s0Gs0@s0(#Gj#As0I#j#Bs0S#V#S#Gj##s0V#j##s1##=s1$s0ws0a#Gj#Bs1&#j#Cs12#V#S#Gj##s15#j##s1`#=s1as1Vs1B#Gj#Cs1c#j#Ds1q#V#S#Gj##s1t#j##s2E#=s2Fs29s2'#Gj#Ds2H#j#Es2X#V#S#Gj##s2[#j##s3.#=s3/s2|s2l#Gj#Es31#j#Fs3C#V#S#Gj##s3F#j##s3w#=s3xs3gs3Y#Gj#Fs3z#j#Gs42#V#S#Gj##s45#j##s4h#=s4is4Vs4J#Gj#Gs4k#j#Hs5%#V#S#Gj##s5(#j##s5]#=s5^s5Is5?#Gj#Hs5`#j#Is5x#V#S#Gj##s5{#j##s6V#=s6Ws6@s68#Gj#Is6Y#j#1s6s#V#S#Gj##s6v#j##s7S#=s7Ts7;s75#Gj#1s7V#j#Js7r#V#S#Gj##s7u#j##s8T#=s8Us8:s86#Gj#Js8W#j#Ks8u#V#S#Gj##s8x#j##s:C#=s:Ds9=s9;#SWUSfSSm#$#l#Ls:Ss:O#j#%s<(#j#Ms>}#j#Ns?##j#Os?%#j#Ps?'#j#<T|#j#&s?5##"). Qed.

(* [comment removed for export] *)
Definition AXStatics2_img_ok : bool :=
  forallb (fun ac : Z * list Z =>
             match image_bytes bsegs (fst ac) (8 * length (snd ac))%nat with
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
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.XS.AXStatics2_img_ok)|] Array.empty "##&###(#'#(#&#)#*#VECDWFCGDm$$##"). Qed.

(* [comment removed for export] *)
Lemma AXStatics2_AXStatics : forall m, AXStatics2 m -> AXStatics m.
Proof. intros m XS. unfold AXStatics2 in XS. destruct XS as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ACanaryReads (m : mem) : Prop :=
  Lib.PropExec.rdn bsegs m (Z_to_bv 64 AG_GOT_STACK_CHK) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 AG_STACK_CHK_GUARD))
  /\ exists can : Z, Lib.PropExec.rdn bsegs m (Z_to_bv 64 AG_STACK_CHK_GUARD) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).

End XS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RBL.
  Context {HCEIL : HeapCeil}.

Record rbnode := mkRBN { rbn_parent : Z ; rbn_left : Z ; rbn_right : Z ; rbn_color : Z }.
Definition RBnodeCells (n : rbnode) (pad : list byte) : list cell :=
  [C8 (wz (rbn_parent n)); C8 (wz (rbn_left n)); C8 (wz (rbn_right n)); C4 (wz (rbn_color n)); CB 4 pad].
Definition ARBcells (m : mem) (ns : gmap Z rbnode) : Prop :=
  map_Forall (fun (a : Z) (n : rbnode) => exists pad, rw_cells bsegs m a (RBnodeCells n pad)) ns.

Record dlnode := mkDLN { dl_next : Z ; dl_prev : Z }.
Definition DLnodeCells (n : dlnode) : list cell := [C8 (wz (dl_next n)); C8 (wz (dl_prev n))].
Definition ADLcells (m : mem) (ls : gmap Z dlnode) : Prop :=
  map_Forall (fun (a : Z) (n : dlnode) => rw_cells bsegs m a (DLnodeCells n)) ls.

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
Lemma ARBcells_lookup : forall m ns a n, ARBcells m ns -> ns !! a = Some n -> exists pad, rw_cells bsegs m a (RBnodeCells n pad).
Proof. intros m ns a n H L. exact (map_Forall_lookup_1 _ _ _ _ H L). Qed.
Lemma ADLcells_lookup : forall m ls a n, ADLcells m ls -> ls !! a = Some n -> rw_cells bsegs m a (DLnodeCells n).
Proof. intros m ls a n H L. exact (map_Forall_lookup_1 _ _ _ _ H L). Qed.

End RBL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KIT.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma rw_cells_recells : forall m A cs cs',
  rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells bsegs m A cs'.
Proof.
  intros m A cs cs' [[WF B] W] WF' EB ES. split; [split|].
  - exact WF'.
  - rewrite EB. exact B.
  - rewrite ES. exact W.
Qed.

(* [comment removed for export] *)
Lemma APMutex_of_zero : forall m a, rw_cells bsegs m a PMutexZeroCells -> a mod 4 = 0 -> APMutex m a 0.
Proof.
  intros m a H Ha. split; [| split; [left; reflexivity| exact Ha]].
  eapply rw_cells_recells; [exact H | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.
Lemma APCond_of_zero6 : forall m a, rw_cells bsegs m a [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> a mod 8 = 0 -> APCond m a 0.
Proof.
  intros m a H Ha. split; [| split; [left; reflexivity| exact Ha]].
  eapply rw_cells_recells; [exact H | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma le8_firstn4 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Lemma C8_read_low4 : forall m A (w : word) cs,
  rw_cells bsegs m A (C8 w :: cs) -> ov_read_bytes bsegs m (wa A) 4 = Some (le4 w).
Proof.
  intros m A w cs [[WF B] _].
  pose proof (bytes_at_ov_read bsegs m A _ 0 4 B) as R. rewrite Z.add_0_r in R.
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
  APMutex m a lk -> munch W m m' -> wmono bsegs m m' -> disjoint_from W a SZ_PMUTEX -> APMutex m' a lk.
Proof.
  intros W m m' a lk (C & L & A) MU WM D. split; [| split; assumption].
  unfold PMutexCells, zeros, SZ_PMUTEX in *. xtransport MU WM D.
Qed.

Lemma APCond_transport : forall W m m' a clk,
  APCond m a clk -> munch W m m' -> wmono bsegs m m' -> disjoint_from W a SZ_PCOND -> APCond m' a clk.
Proof.
  intros W m m' a clk (C & L & A) MU WM D. split; [| split; assumption].
  unfold PCondCells, zeros, SZ_PCOND in *. xtransport MU WM D.
Qed.

Lemma AErrCode_transport : forall W m m' a E,
  AErrCode m a E -> munch W m m' -> wmono bsegs m m' -> disjoint_from W a SZ_EC -> AErrCode m' a E.
Proof.
  intros W m m' a E (C & OK) MU WM D. split; [| exact OK]. unfold ErrCodeCells, SZ_EC in *. xtransport MU WM D.
Qed.

Lemma AFlatBuf_transport : forall W LB m m' a F ds,
  AFlatBuf LB m a F ds -> munch W m m' -> wmono bsegs m m' -> disjoint_from W a SZ_FB ->
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
  AAllocImpl LB m a -> munch W m m' -> wmono bsegs m m' -> disjoint_from W a SZ_ALLOCIMPL ->
  disjoint_from W (sh a) (nsh SZ_ALLOCIMPL) -> AAllocImpl LB m' a.
Proof.
  intros W LB m m' a (p & junk & IN & C & RB & AD) MU WM D DS. exists p, junk. split; [exact IN|].
  split; [| split; [exact RB| eapply addressable_transport; [exact AD| exact MU| exact WM| exact DS]]].
  unfold SZ_ALLOCIMPL in *. xtransport MU WM D.
Qed.

Lemma ARegistry_transport : forall W LB m m' r owner first lk,
  ARegistry LB m r owner first lk -> munch W m m' -> wmono bsegs m m' -> disjoint_from W r NEWSZ_REG ->
  disjoint_from W (sh r) (nsh NEWSZ_REG) -> ARegistry LB m' r owner first lk.
Proof.
  intros W LB m m' r owner first lk (p & j0 & j7 & IN & C0 & PM & C1 & C2 & RB & AD) MU WM D DS. exists p, j0, j7.
  assert (AD' : addressable m' r NEWSZ_REG) by (eapply addressable_transport; [exact AD| exact MU| exact WM| exact DS]).
  clear AD DS. unfold NEWSZ_REG, O_REG_MUTEX, O_REG_OWNER, SZ_REG, CookieCells, zeros in *.
  split; [exact IN|]. split; [xtransport MU WM D|]. split.
  { eapply APMutex_transport; [exact PM| exact MU| exact WM| eapply disjoint_from_sub; [exact D| lia| unfold SZ_PMUTEX; lia]]. }
  split; [xtransport MU WM D|]. split; [xtransport MU WM D|]. split; [exact RB| exact AD'].
Qed.
Scheme kc__3 := Elimination for Corelib.Init.Logic.ex Sort Prop.

Lemma AConfigSvc_transport : forall W LB m m' c S,
  AConfigSvc LB m c S -> munch W m m' -> wmono bsegs m m' -> disjoint_from W c NEWSZ_CFG ->
  disjoint_from W (sh c) (nsh NEWSZ_CFG) -> AConfigSvc LB m' c S.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.block); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.svch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AConfigSvc); constr:(HCEIL); constr:(@kc__3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.bptr); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.NEWSZ_CFG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@Corelib.Init.Datatypes.app); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SvcHdrCells); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.CookieCells); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_vptr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVP_CONFIG_SVC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_destroy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.P_A_DESTROY_ALLOC_CONFIG); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPres.rblock_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.addressable); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.nsh); constr:(@kc__2); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.addressable_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_ti); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_id); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_owner); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_next); constr:(@Corelib.Lists.ListDef.repeat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.KIT.disjoint_from_sub); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@kc__3 ((@Corelib.Init.Datatypes.list) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))); constr:(@kc__3 (@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.bptr))|] [|@j7; @j4; @p; @__ff; @__varmap; @__wit; @__x1; @__arith; @x; @y; @m; @n; @AD'; @DS; @D; @WM; @MU; @AD; @RB; @H; @E2; @E1; @C; @IN; @S; @c; @m'; @LB; @W|] "#+d#P$U#\#g#k#_###i#a#|#J#z#,#-#1#$#I#+#.#0#K#(#*#)#4#/#5#'#%#8#<#3#9#=#@#L#2#6#A#D#7#:#>#E#H#&#F#;#B#C#G#M$?#Z#?#N$@$7$N$L#X#W#e#v$4$9$A$C$<$>$D$H$I$U#T#U#[#q#p#n#u$'#O$+$.$/$0$1$3$2$8$:$;$=$B$E$J$K$F$P$R$S$T$Q$O$W$V$M$5$,#]#V#c#t#x#j#f#m#~#}#{#y#h#l$%#d#b#s#^$#$$$&#w#o#Y$-$G$*$(#S#r$6$)#`F$5%$6$$7&$8&$9'$:&$;&$<&$=$$>$$?'$@$$A&$B&$C%$D%$E($F&$G&$H$$I$$J$#\%$K$$L$$M%#[%$N'$O($P$$Q$$R$#Z$$S'$T(@S[@S\:SF:#:#:#:#:#USM#USN#USM(USN#US]#k##&#3FS,S>PG@&VSOICVSO#C'ICS-S&'%C#D0%#R.S,A6A3VS^$#ASFVS_$#8#US`#$Sa$#$#$#2#PUSPE(E$#(E*#7G&E$#&E4#-HS'S&#,S,%C#L+S,%C#J*FS&D)S'S&D#$##&##)##,##A#j#$s#'#1s#(#j#%s#)#1s#*#j#&I#1I#4S'S&S,5HS(S&/MS&D6S(USbD/N$#3FNRS'S(k##$#k##(#k##*#k##,#j##.#'ICS-S('s#9C#D0s#9#M.S&&E#s#&-HRS(#,S&%C#L+S&%C#J*FS(D)RS(D#$##&##)##,##0#j#$s#J#1s#K#j#%s#L#1s#M#j#&I#U#G'ICS-S''s#PC#D0s#P#N.S(&E#s#=-HMS'#,S(%C#L+S(%C#J*FS'D)MS'D#$##&##)##,##0#j#$s#a#1s#b#j#%s#c#1s#d#'ICS>R's#eC#D0s#e#S#.S'&E#s#R-HNR#,S'%C#L+S'%C#J*FRD)NRD#$##&##)##,##0#j#$s#v#1s#w#j#%s#x#1s#y#4S#MR5HNM/S$MD6N/O#s#O3FOS*S#Nk##$#k##'#k##)#k##+#j##-#'ICS,M's$)C#D0s$)#S*.R&E#s#r-HS#M#,R%C#L+R%C#J*FMD)S#MD#$##&##)##,##0#j#$s$:#1s$;#j#%s$<#U#G'ICS&N's$>C#D0s$>#S$.M&E#s$+-HS*N#,M%C#L+M%C#J*FND)S*ND#$##&##)##,##0#j#$s$O#1s$P#'ICS(S#'s$QC#D0s$Q#O.N2s$DS-(E#s$C(Es$J#&E#s$B&E'#-HS$S##,N%C#L+N%C#J*FS#D)S$S#D#$##&##)##,##4#j#$s$f#1s$g#4S5S$S*5HOS$/S)S$D6O/S+#s$=3FS+S0S5Ok##$#k##'#k##)#k##+#j##-#'ICS'S*'s$sC#D0s$s#S5.S#2s$fS>(E#s$e(Es$l#&E#s$d&E'#-HOS*#,S#%C#L+S#%C#J*FS*D)OS*D#$##&##)##,##4#j#$s%,#U#G'ICRS$'s%.C#D0s%.#S0.S*2s$}S,(E#s$|(Es%'#&E#s${&E'#-HS5S$#,S*%C#L+S*%C#J*FS$D)S5S$D#$##&##)##,##4#'ICMO's%CC#D0s%C#S).S$2s%6S&(E#s%5(Es%<#7P&E$#&E(#-HS0O#,S$%C#L+S$%C#J*FOD)S0OD#$##&##)##,##5#4S6S)S05HS+S)/S.S)D6S+/S1#s%.3FS1S9S6S+k##$#k##'#k##)#k##+#j##-#.O2s%TS((E#s%S(Es%Z#7S-&E$#&E(#-HS)S5#,O%C#L+O%C#J*FS5D)S)S5D#$##&##)##,#'ICS#S0's%vC#D0s%v#S6.S02s%iR(E#s%h(Es%o#7S,&E$#&E(#-HS6S)#,S0%C#L+S0%C#J*FS)D)S6S)D#$##&##)##,#.S)2s%{M(E#s%z(Es&%#7S&&E$#&E(#-HS9S+#,S)%C#L+S)%C#J*FS+D)S9S+D#$##&##)##,#4S:S.S95HS1S./S/S.D6S1/S2#s%r3FS2S@S:S1k##$#k##'#k##)#k##+#j##-#,S+%C#L+S+%C#J*FS6D)S.S6D#$##&##)#.S62s&ES#(E#s&D(Es&K#7S'&E$#&E(#-HS1S9#,S9%C#L+S9%C#J*FS.D)S:S.D#$##&##)#,S.%C#L+S.%C#J*FS1D)S@S1D#$##&##)#4S;S/S@5HS2S//S3S/D6S2/S7#s&D3FS7SGS;S2k##$#k##'#k##)#k##+#j##-#+S1%C#J*FS:D)S/S:D#$##&#,S:%C#L+S@%C#J*FS/D)S;S/D#$##&#+S/%C#J*FS2D)SGS2D#$##&#4SAS3SG5HS7S3/S8S3D6S7/S<#s&c3FS<SBSAS7k##$#k##'#k##)#k##+#j##-#*FS;D)S3S;D#$#+S;%C#J*FS3D)SAS3D#$#*FS7D)SBS7D#$#4S?S8SB5HS<S8/S=S8D6S</Q#s&y3FQSCS?S<k##$#k##'#k##)#k##+#j##-#)S8SAD*FSBD)S?S8D4QSCS?5HS=SC/S%SCD6S=/S4#s'+'ICS-S4's'[C#D0s'[#Sc.S%&E#s'H-HSDS4#,S%%C#L+S%%C#J*FS4D)SDS4D#$##&##)##,##0#j#$s'l#1s'm#j#%s'n#1s'o#j#&I#'ICS?S%'s'qC#D0s'q#SH.K&E#s'^-HS4S%#,K%C#L+K%C#J*FS%D)S4S%D#$##&##)##,##0#j#$s(&#1s('#j#%s((#'ICS<K's()C#D0s()#SD.Q2s'xS7(E#s'w(Es'~#&E#s'v&E'#-HS%K#,Q%C#L+Q%C#J*FKD)S%KD#$##&##)##,##4#j#$s(>#'ICS8Q's(?C#D0s(?#S4.S=2s(2S3(E#s(1(Es(8#7S/&E$#&E(#-HKQ#,S=%C#L+S=%C#J*FQD)KQD#$##&##)##,#]SdSDS%KQDS,S>S-G7S2&Es#)#&Es#-#-HS%K#8s#(;#USeQ8#;#USfQ8#;#USgQ8#;#UShQ8#;#8s#4;#(E#s(V(E&#(E*#(E.#(E2#(E6#$s(^$#$#$#USiSQWSjs(x#$2%#2'S2(E#s(d(E%#&Es#L#&E.#Bs)*B#B#A#USk'C#USPSR@SRVSlCPUSmCUSnCVSoCSFXSSC#ST#[SU%SVSESESI#SWVSp&SI<SXSYVSqGS-%SX#SYm$%#WSrCSQPXSsGS-$#l#'*)#l#(0/#l#)32#j#*C#9GGk#*C#UGS%l#+&$#9KKm#$#$s#*$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#C#=K#=Ks#_9$#9$$j#,CG9PGUSt#j#-C#j#,C#=PGXSuCCSv#<C#j#.C#j#/C#<CKCG<C#j#,SZ#<Cs#p`SwSZCCCSJSJ11$7s#q#fSxCCCCCCSK222SK)KK(7s#r#<C6`SyCCSL4SL087$77#VSzCs#uWS{Cs#n#XSSC#ST#[SUs#qSVSESESI#SWl#'#s#ns#hl#(s#us#t#l#)s#xs#w#j#*C#=Gs#}9##k#*C#l#+&#s#hXS|s##B/#=Ks$$9#s#&m#%#\S}SHKs$)Ks$'S-s#j#^S~HSHS4S%Ks$.S+S,S>#m##s$Q>s$ss$rS(G>s$us$rN#>s$xs$rO#>s$Us$r&#l#0s$Zs$_#>s$ns$\S.#Ds*Rs$rS/#Ds*Ss%-S3#DIs%BS8#j#1s%Y#j#2s%\#j#3s%^#j#4s%`#j#5s%b#j#6s%d#V#PGj##s%g#j##s%v#?s%ws%vs%j#Gj#7s%y#j#8s%}#V#PGj##s&%#j##s&8#?s&9s&6s&*#Gj#7s&<#j#9s&C#V#PGj##s&G#j##s&`#?s&as&[s&O#Gj#7s&d#j#:s&n#V#PGj##s&x#j##s';#?s'<s'3s''#Gj#7s'E#j#;s'X#V#PGj##s']#j##s(2#?s(3s'}s'q#Gj#7s(7#j#$s*x#V#PGj##s(O#j#,s*{#Es*|s(ts(h#Gj#7s)/#j#%s*~#V#PGj##s)E#j#,s+%#Es+&s)hs)\#Gj#7s)}#j#&I#V#PGj##s*9#j#,I#EIs*_s*R#Gj#7s+.#j#<T##j#=C#j#>s+2#j#.T$#j#?s+@#j#@s+B##"). Qed.

Lemma AStreamSvc_transport : forall W LB m m' v S implb,
  AStreamSvc LB m v S implb -> munch W m m' -> wmono bsegs m m' -> disjoint_from W v NEWSZ_SSVC ->
  disjoint_from W (sh v) (nsh NEWSZ_SSVC) -> AStreamSvc LB m' v S implb.
Proof.
  intros W LB m m' v S implb (p & j7 & IN & C & E1 & E2 & RB & AD) MU WM D DS. exists p, j7. split; [exact IN|].
  assert (AD' : addressable m' v NEWSZ_SSVC) by (eapply addressable_transport; [exact AD| exact MU| exact WM| exact DS]).
  clear AD DS. split; [| split; [exact E1| split; [exact E2| split; [exact RB| exact AD']]]].
  unfold NEWSZ_SSVC, SvcHdrCells, CookieCells, zeros in *. xtransport MU WM D.
Qed.

Lemma AScheduler_transport : forall W LB m m' s S,
  AScheduler LB m s S -> munch W m m' -> wmono bsegs m m' -> disjoint_from W s NEWSZ_SCH ->
  disjoint_from W (sh s) (nsh NEWSZ_SCH) -> AScheduler LB m' s S.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.block); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.schv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AScheduler); constr:(HCEIL); constr:(@kc__3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.bptr); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.NEWSZ_SCH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SvcHdrCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sch_hdr); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_SCH_ONE_THREAD); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_SCH_MUTEX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.APMutex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_SCH_PMUTEX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sch_lk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_SCH_SPIN); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_SCH_EVENT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.APCond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_SCH_COND); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.CLOCK_MONOTONIC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_SCH_EVSTATE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.P_A_SCHED_GET_DEFAULT_TASK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sch_stopped); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sch_shutdown); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.u64max); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_SCH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.CookieCells); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_vptr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVP_SCHED); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_destroy); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.P_A_DESTROY_ALLOC_SCHED); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPres.rblock_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.addressable); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.nsh); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.addressable_transport); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_ti); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_id); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_owner); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.sv_next); constr:(@Corelib.Lists.ListDef.repeat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.KIT.disjoint_from_sub); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.KIT.APMutex_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_PMUTEX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.KIT.APCond_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_PCOND)|] [|@j7; @j219; @jt; @je; @j109; @jm; @j50; @p; @__ff; @__varmap; @__wit; @__x1; @__arith; @x; @y; @m; @n; @E; @AD'; @DS; @D; @WM; @MU; @AD; @RB; @H; @E4; @E3; @E2; @E1; @C6; @C5; @PC; @C4; @C3; @PM; @C2; @C1; @C0; @IN; @S; @s; @m'; @LB; @W|] "#_e$7%O$V$C$P$N$[$F##$u$s$o$i$h$g$+$e$a$,$_$/$H$]$T#1#5#9#=#0#4#8#<#@#A#D#E$-#3#7#;#?%6#/#C#H#2#6#:#>#B#$#-#J#L$.#F$2$1$0#P#G#T$3#.#N#I#M#X#Q#R%7#K#V#\%:%5%;#'#(#U#O#Y#`#,#S#Z#]$S%C#&#a#d#W#^#e#f#[#h#i#_#b#m#p$4#*#)#c#l#t#+#g#k#q#u#x#z$)$*%.#j#n#r#v#y#|#}#o#~$$$&%,#%#s$%$#$'#w$(%K$:$A#{%J$\$?$>$L%0%?%@%O%Q$;$<$B$Y$b$k$n$}%#$6$5%'%(%)%*%+%1%2%4%9%<%A%B%=%F%H%I%N%P$D$=$U$J$q$O$W$v$Z$I$X$x$w$m$l$M$R$t$r$f$^${$`$Q$K$p$@$E$y$z$|%8%3%L%$%>$~$d%M%&$c$j%-%%$G%/%G%E%DU$|&$}%#x%$~&%#'%$%%%%%&$%'%%($%)&%*&%+$%,$%-'%.$%/$%0$%1&#y%%2&%3&%4$%5$%6&%7$%8$%9(%:&%;&%<$%='%>*%?&%@'%A%%B(%C$$;$%D%%E$%F$%G$%H+%I'%J(%K$%L5%M/%N'UT@TMUT@TN=TA=#=#=#=#=#UTE#UTF#UTE(UTF#UTO#k##&#>HS^SjSCIUT@&VTGS&DVTG#D1S&DSySD1%D#F;%#S-2Sd:#'ES;SD#%SDS(,TP,#*GUTD3#4$##5%#('#,(,#,#,#(#SzUTDC#C$##C*#'ES;2#%SDS',),#(#S_#C#*'ES;'#%SDS$9Sd7S;$#%SDRLGUTQ#HTA*##s#.#=(A#(;S^#C#7#C%##C*#'ES;-#%SDQ(6Sj#C#='ES;%#%SDO5S;#N%SDMM4LTRM#(s#)T80Sd*#/Sd*##s#D#s#3#s#E&##s#F;#(s#2#(s#1SCLTSM##C1s#1#C$##C%##C4##C5##C6##C+##C-##C6##Cs#+##C;##C<##C;##C>##C?#'ES;A#%SDL<I'ES;$#4s#T&D#K3s#V&D#J&Ds#$G&Ds#%s#9)$#&Ds#%G&Ds#&s#<)$#.HSDF-S;SDF$$#$&#$*#$.#$1#$4#$8#$s#9#$s#<#$s#A#$s#N#$s#R#$s#Y#$s#k#$s#o#j#$s#u#+s#v#j#%s#w#+s#x#j#&s#y#+s#z#j#'s#{#+s#|#j#(s#}#+s#~#j#)s$##+s$$#j#*s$%#+s$&#j#+S&#+S&#?SyS_S^@ESzS_8SdS_FASzUTTF8SD$#>HSDS~SySzk##$#k##(#k##*#k##,#j##.#1S&DSySP1s$5D#F;s$5#S)2SD:#'ES-SP#%SPS('ES-#s$$%SPS''ES-#s#|%SPS$9SD7S-$#%SPR'ES-#s#r%SPQ'ES-#s#p%SPO5S-#N%SPM0SD*#/SD*##s$Q#s$@#s$R&##s$Ss$(#(s$?##C#s#b#Cs#u##Cs$.##Cs#z##Cs#{##Cs#z##Cs#}##Cs#~#'ES-3#%SPL'ES-#s#a4s#&&D#K3s#(&D#J&D9G&D:s$;)$#&D:G&D;s$>)$#.HSPF-S-SPF$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#=#$s#A#j#$s$w#+s$x#j#%s$y#+s$z#j#&s${#+s$|#j#'s$}#+s$~#j#(s%##+s%$#j#)s%%#+s%&#j#*s%'#+s%(#j#+S&#U#I1S&DSyS;1s%+D#F;s%+#S>2SP:#'ES)S;#%S;S('ES)#s$v%S;S''ES)#s$r%S;S$9SP7S)$#%S;R'ES)#s$h%S;Q'ES)#s$f%S;O5S)#N%S;M0SP*#/SP*##s%G#s%6#s%H&##s%Is$z#(s%5##C#s$X#Cs$k##Cs%$##Cs$p##Cs$q##Cs$p##Cs$s##Cs$t#'ES)3#%S;L'ES)#s$W4s#&&D#K3s#(&D#J&D9G&D:s%1)$#&D:G&D;s%4)$#.HS;F-S)S;F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#=#$s#A#j#$s%m#+s%n#j#%s%o#+s%p#j#&s%q#+s%r#j#'s%s#+s%t#j#(s%u#+s%v#j#)s%w#+s%x#j#*s%y#+s%z#1S&DS~S-1s%{D#F;s%{#S62S;:#'ES>S-#%S-S('ES>#s%j%S-S''ES>#s%f%S-S$9S;7S>$#%S-R'ES>#s%\%S-Q'ES>#s%Z%S-O5S>#N%S-M0S;*#/S;*##s&;#s&*#s&<&##s&=s%n#(s&)##C#s%L#Cs%_##Cs%t##Cs%d##Cs%e##Cs%d##Cs%g##Cs%h#'ES>3#%S-L'ES>#s%K4s#&&D#K3s#(&D#J&D9G&D:s&%)$#&D:G&D;s&()$#.HS-F-S>S-F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#=#$s#A#j#$s&a#+s&b#j#%s&c#+s&d#j#&s&e#+s&f#j#'s&g#+s&h#j#(s&i#+s&j#j#)s&k#+s&l#j#*s&m#+s&n#?SPSdS~@ESDSd8S-SdFASD8S)#s%H>HS)S;SPSDk##$#k##'#k##)#k##+#j##-#1S&DSdS)1s&zD#F;s&z#S.2S-:#'ES6S)#%S)S('ES6#s&i%S)S''ES6#s&e%S)S$9S-7S6$#%S)R'ES6#s&[%S)Q'ES6#s&Y%S)O5S6#N%S)M0S-*#/S-*##s':#s')#s';&##s'<s&m#(s'(##C#s&K#Cs&^##Cs&s##Cs&c##Cs&d##Cs&c##Cs&f##Cs&g#'ES63#%S)L'ES6#s&J4s#&&D#K3s#(&D#J&D9G&D:s'$)$#&D:G&D;s'')$#.HS)F-S6S)F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#=#$s#A#j#$s'`#+s'a#j#%s'b#+s'c#j#&s'd#+s'e#j#'s'f#+s'g#j#(s'h#+s'i#j#)s'j#+s'k#j#*s'l#U#I1S&DSDS>1s'nD#F;s'n#S*2S):#'ES.S>#%S>S('ES.#s']%S>S''ES.#s'Y%S>S$9S)7S.$#%S>R'ES.#s'O%S>Q'ES.#s'M%S>O5S.#N%S>M0S)*#/S)*##s(.#s'y#s(/&##s(0s'a#(s'x##C#s'?#Cs'R##Cs'g##Cs'W##Cs'X##Cs'W##Cs'Z##Cs'[#'ES.3#%S>L'ES.#s'>4s#&&D#K3s#(&D#J&D9G&D:s't)$#&D:G&D;s'w)$#.HS>F-S.S>F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#=#$s#A#j#$s(T#+s(U#j#%s(V#+s(W#j#&s(X#+s(Y#j#'s(Z#+s([#j#(s(\#+s(]#j#)s(^#+s(_#1S&DSPS61s(`D#F;s(`#S?2S>:#'ES*S6#%S6S((s(SSy#C#s(R#Cs(Y#'ES*&#%S6S''ES*#s(N%S6S$9S>7S*$#%S6R'ES*#s(D%S6Q'ES*#s(B%S6O5S*#N%S6M0S>*#/S>*##s)##s(n#s)$&##s)%s(V#(s(m##C#s(4#Cs(G##Cs(\##Cs(L##Cs(M##Cs(L##Cs(O##Cs(P#'ES*3#%S6L'ES*#s(34s#)&D#K3s#+&D#J&D9G&D:s(i)$#&D:G&D;s(l)$#.HS6F-S*S6F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#@#$s#D#j#$s)I#+s)J#j#%s)K#+s)L#j#&s)M#+s)N#j#'s)O#+s)P#j#(s)Q#+s)R#j#)s)S#+s)T#?S>S-S;@ES)S-8S.S-FAS)8S*#s(.>HS*S6S>S)k##$#k##'#k##)#k##+#j##-#1S&DS;S.1s)`D#F;s)`#S72S6:#'ES?S.#%S.S((s)SS~#C#s)R#Cs)Y#'ES?&#%S.S''ES?#s)N%S.S$9S67S?$#%S.R'ES?#s)D%S.Q'ES?#s)B%S.O5S?#N%S.M0S6*#/S6*##s*##s)n#s*$&##s*%s)V#(s)m##C#s)4#Cs)G##Cs)\##Cs)L##Cs)M##Cs)L##Cs)O##Cs)P#'ES?3#%S.L'ES?#s)34s#)&D#K3s#+&D#J&D9G&D:s)i)$#&D:G&D;s)l)$#.HS.F-S?S.F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#@#$s#D#j#$s*I#+s*J#j#%s*K#+s*L#j#&s*M#+s*N#j#'s*O#+s*P#j#(s*Q#+s*R#j#)s*S#U#I1S&DS-S*1s*UD#F;s*U#S/2S.:#'ES7S*#%S*S((s*HSd#C#s*G#Cs*N#'ES7&#%S*S''ES7#s*C%S*S$9S.7S7$#%S*R'ES7#s*9%S*Q'ES7#s*7%S*O5S7#N%S*M0S.*#/S.*##s*t#s*c#s*u&##s*vs*K#(s*b##C#s*)#Cs*<##Cs*Q##Cs*A##Cs*B##Cs*A##Cs*D##Cs*E#'ES73#%S*L'ES7#s*(4s#)&D#K3s#+&D#J&D9G&D:s*^)$#&D:G&D;s*a)$#.HS*F-S7S*F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#@#$s#D#j#$s+>#+s+?#j#%s+@#+s+A#j#&s+B#+s+C#j#'s+D#+s+E#j#(s+F#+s+G#1S&DS)S?1s+HD#F;s+H#S+2S*:#'ES/S?#%S?S((s+;SD#C#s+:#Cs+A#'ES/&#%S?S'(s+8Sz#C#s+?'ES/%#%S?S$9S*7S/$#%S?R'ES/#s+.%S?Q'ES/#s+,%S?O5S/#N%S?M0S**#/S**##s+i#s+X#s+j&##s+ks+@#(s+W##C#s*z#Cs+1##Cs+F##Cs+6##Cs+7##Cs+6##Cs+9##Cs+:#'ES/3#%S?L'ES/#s*y4s#+&D#K3s#-&D#J&D9G&D:s+S)$#&D:G&D;s+V)$#.HS?F-S/S?F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#<#$s#B#$s#F#j#$s,3#+s,4#j#%s,5#+s,6#j#&s,7#+s,8#j#'s,9#+s,:#j#(s,;#+s,<#?S?S.S6@ES*S.8S/S.FAS*8S+#s*r>HS+S7S?S*k##$#k##'#k##)#k##+#j##-#1S&DS>S71s,HD#F;s,H#S@2S?:#'ES+S7#%S7S((s,;SP#C#s,:#Cs,A#'ES+&#%S7S'(s,8Sy#C#s,?'ES+%#%S7S$9S?7S+$#%S7R'ES+#s,.%S7Q'ES+#s,,%S7O5S+#N%S7M0S?*#/S?*##s,i#s,X#s,j&##s,ks,@#(s,W##C#s+z#Cs,1##Cs,F##Cs,6##Cs,7##Cs,6##Cs,9##Cs,:#'ES+3#%S7L'ES+#s+y4s#+&D#K3s#-&D#J&D9G&D:s,S)$#&D:G&D;s,V)$#.HS7F-S+S7F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#<#$s#B#$s#F#j#$s-3#+s-4#j#%s-5#+s-6#j#&s-7#+s-8#j#'s-9#+s-:#j#(s-;#U#I1S&DS6S/1s-=D#F;s-=#S82S7:#'ES@S/#%S/S((s-0S;#C#s-/#Cs-6#'ES@&#%S/S'(s--S~#C#s-4'ES@%#%S/S$9S77S@$#%S/R'ES@#s-#%S/Q'ES@#s,}%S/O5S@#N%S/M0S7*#/S7*##s-^#s-M#s-_&##s-`s-5#(s-L##C#s,o#Cs-&##Cs-;##Cs-+##Cs-,##Cs-+##Cs-.##Cs-/#'ES@3#%S/L'ES@#s,n4s#+&D#K3s#-&D#J&D9G&D:s-H)$#&D:G&D;s-K)$#.HS/F-S@S/F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#<#$s#B#$s#F#j#$s.(#+s.)#j#%s.*#+s.+#j#&s.,#+s.-#j#'s..#+s./#1S&DS.S+1s.0D#F;s.0#S02S/:#'ES8S+#%S+S((s.#S-#C#s-~#Cs.)#'ES8&#%S+S'(s-|Sd#C#s.''ES8%#%S+S$9S/7S8$#%S+R(s.2S_#C#s..#Cs-x##Cs-}#'ES8'#%S+Q'ES8#s-t%S+O5S8#N%S+M0S/*#/S/*##s.U#s.D#s.V&##s.Ws.,#(s.C##C#s-f#Cs-y##Cs.2##Cs-~##Cs.###Cs-~##Cs.%##Cs.&#'ES83#%S+L'ES8#s-e4s#/&D#K3s#1&D#J&D9G&D:s.?)$#&D:G&D;s.B)$#.HS+F-S8S+F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#7#$s#;#$s#@#$s#F#$s#J#j#$s.{#+s.|#j#%s.}#+s.~#j#&s/##+s/$#j#'s/%#+s/&#?S@S/S7@ES+S/8S0S/FAS+8S,#s-\>HS,S8S@S+k##$#k##'#k##)#k##+#j##-#1S&DS*S@1s/2D#F;s/2#S,2S+:#'ES0S@#%S@S((s/%S)#C#s/$#Cs/+#'ES0&#%S@S'(s.~SD#C#s/)'ES0%#%S@S$9S+7S0$#%S@R(s/4Sz#C#s/0#Cs.z##Cs/##'ES0'#%S@Q'ES0#s.v%S@O5S0#N%S@M0S+*#/S+*##s/W#s/F#s/X&##s/Ys/.#(s/E##C#s.h#Cs.{##Cs/4##Cs/$##Cs/%##Cs/$##Cs/'##Cs/(#'ES03#%S@L'ES0#s.g4s#/&D#K3s#1&D#J&D9G&D:s/A)$#&D:G&D;s/D)$#.HS@F-S0S@F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#7#$s#;#$s#@#$s#F#$s#J#j#$s/}#+s/~#j#%s0##+s0$#j#&s0%#+s0&#j#'s0'#U#I1S&DS?S81s0)D#F;s0)#SA2S@:#'ES,S8#%S8S((s/xS>#C#s/w#Cs/~#'ES,&#%S8S'(s/uSP#C#s/|'ES,%#%S8S$9S@7S,$#%S8R(s0+Sy#C#s0'#Cs/q##Cs/v#'ES,'#%S8Q'ES,#s/m%S8O5S,#N%S8M0S@*#/S@*##s0N#s0=#s0O&##s0Ps0%#(s0<##C#s/_#Cs/r##Cs0+##Cs/w##Cs/x##Cs/w##Cs/z##Cs/{#'ES,3#%S8L'ES,#s/^4s#/&D#K3s#1&D#J&D9G&D:s08)$#&D:G&D;s0;)$#.HS8F-S,S8F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#7#$s#;#$s#@#$s#F#$s#J#j#$s0t#+s0u#j#%s0v#+s0w#j#&s0x#+s0y#1S&DS7S01s0zD#F;s0z#S92S8:#'ESAS0#%S0S((s0mS6#C#s0l#Cs0s#'ESA&#%S0S'(s0jS;#C#s0q'ESA%#%S0S$9S87SA$#%S0R(s0|S~#C#s0x#Cs0f##Cs0k#'ESA'#%S0Q(s0wS^#C#s0~'ESA%#%S0O5SA#N%S0M0S8*#/S8*##s1E#s14#s1F&##s1Gs0x#(s13##C#s0V#Cs0i##Cs0~##Cs0n##Cs0o##Cs0n##Cs0q##Cs0r#'ESA3#%S0L'ESA#s0U4s#1&D#K3s#3&D#J&D9G&D:s1/)$#&D:G&D;s12)$#.HS0F-SAS0F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#2#$s#9#$s#=#$s#B#$s#H#$s#L#j#$s1k#+s1l#j#%s1m#+s1n#j#&s1o#+s1p#?SAS0S8@ES,S08S1S0FAS,8S2#s0J>HS2S9SAS,k##$#k##'#k##)#k##+#j##-#1S&DS/S,1s1|D#F;s1|#S12S0:#'ES9S,#%S,S((s1oS.#C#s1n#Cs1u#'ES9&#%S,S'(s1lS-#C#s1s'ES9%#%S,S$9S07S9$#%S,R(s1~Sd#C#s1z#Cs1h##Cs1m#'ES9'#%S,Q'ES9#s1w%S,O5S9#N%S,M0S0*#/S0*##s2E#s24#s2F&##s2Gs1x#(s23##C#s1V#Cs1i##Cs1~##Cs1n##Cs1o##Cs1n##Cs1q##Cs1r#'ES93#%S,L'ES9#s1U4s#/&D#K3s#1&D#J&D9G&D:s2/)$#&D:G&D;s22)$#.HS,F-S9S,F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#7#$s#;#$s#@#$s#F#$s#J#j#$s2k#+s2l#j#%s2m#+s2n#j#&s2o#U#I1S&DS+SA1s2qD#F;s2q#S22S,:#'ES1SA#%SAS((s2dS*#C#s2c#Cs2j#'ES1&#%SAS'(s2aS)#C#s2h'ES1%#%SAS$9S,7S1$#%SAR(s2sSD#C#s2o#Cs2]##Cs2b#'ES1'#%SAQ'ES1#s*7%SAO5S1#N%SAM0S,*#/S,*##s3:#s3)#s3;&##s3<s2m#(s3(##C#s2K#Cs2^##Cs2s##Cs2c##Cs2d##Cs2c##Cs2f##Cs2g#'ES13#%SAL'ES1#s2J4s#/&D#K3s#1&D#J&D9G&D:s3$)$#&D:G&D;s3')$#.HSAF-S1SAF$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#7#$s#;#$s#@#$s#F#$s#J#j#$s3`#+s3a#j#%s3b#+s3c#1S&DS@S91s3dD#F;s3d#SB2SA:#'ES2S9#%S9S((s3WS?#C#s3V#Cs3]#'ES2&#%S9S'(s3TS>#C#s3['ES2%#%S9S$9SA7S2$#%S9R(s3fSP#C#s3b#Cs3P##Cs3U#'ES2'#%S9Q'ES2#s**%S9O5S2#N%S9M(s3oSj0SA*#/SA*##s4.#s3y#s4/&##s40s3a#(s3x##C#s3?#C,##Cs3g##Cs3W##Cs3X##Cs3W##Cs3Z##Cs3[#'ES24#%S9L'ES2#s3>4s#0&D#K3s#2&D#J&D9G&D:s3t)$#&D:G&D;s3w)$#.HS9F-S2S9F$$#$&#$*#$.#$1#$4#$7#$s#+#$s#.#$s#1#$s#8#$s#<#$s#A#$s#G#$s#K#j#$s4T#+s4U#j#%s4V#+s4W#?SBS1S9@ES2S18S3S1FAS28S4#s31>HS4S<SBS2k##$#k##'#k##)#k##+#j##-#1S&DS8S11s4cD#F;s4c#S<2S9:#'ESBS1#%S1S((s4VS7#C#s4U#Cs4\#'ESB&#%S1S'(s4SS6#C#s4Z'ESB%#%S1S$9S97SB$#%S1R(s4eS;#C#s4a#Cs4O##Cs4T#'ESB'#%S1Q'ESB#s*4%S1O5SB#N%S1M(s4nS^0S9*#/S9*##s5-#s4x#s5.&##s5/s4`#(s4w##C#s4>#C,##Cs4f##Cs4V##Cs4W##Cs4V##Cs4Y##Cs4Z#'ESB4#%S1L'ESB#s4=4s#0&D#K3s#2&D#J&D9G&D:s4s)$#&D:G&D;s4v)$#.HS1F-SBS1F$$#$&#$*#$.#$1#$4#$7#$s#+#$s#.#$s#1#$s#8#$s#<#$s#A#$s#G#$s#K#j#$s5S#+s5T#j#%s5U#U#I1S&DS0S21s5WD#F;s5W#S32S1:#'ES<S2#%S2S((s5JS/#C#s5I#Cs5P#'ES<&#%S2S'(s5GS.#C#s5N'ES<%#%S2S$9S17S<$#%S2R(s5YS-#C#s5U#Cs5C##Cs5H#'ES<'#%S2Q'ES<#s*5%S2O5S<#N%S2M(s5bS_0S1*#/S1*##s5}#s5l#s5~&##s6#s5T#(s5k##C#s52#C,##Cs5Z##Cs5J##Cs5K##Cs5J##Cs5M##Cs5N#'ES<4#%S2L'ES<#s514s#0&D#K3s#2&D#J&D9G&D:s5g)$#&D:G&D;s5j)$#.HS2F-S<S2F$$#$&#$*#$.#$1#$4#$7#$s#+#$s#.#$s#1#$s#8#$s#<#$s#A#$s#G#$s#K#j#$s6G#+s6H#1S&DS,SB1s6ID#F;s6I#S42S2:#'ES3SB#%SBS((s6<S+#C#s6;#Cs6B#'ES3&#%SBS'(s69S*#C#s6@'ES3%#%SBS$9S27S3$#%SBR(s6KS)#C#s6G#Cs65##Cs6:#'ES3'#%SBQ'ES3#s*%%SBO5S3#N%SBM(s6TSz0S2*#/S2*##s6o#s6^#s6p&##s6qs6F#(s6]#(s6\T8#C#s6&#C%##C.##Cs6N##Cs6>##Cs6?##Cs6>##Cs6A##Cs6B#'ES36#%SBL'ES3#s6%4s#2&D#K3s#4&D#J&D;G&D<s6[)$#&D<G&D=s6^)$#.HSBF-S3SBF$$#$&#$*#$.#$1#$4#$7#$s#-#$s#0#$s#3#$s#:#$s#>#$s#C#$s#I#$s#M#j#$s7;#+s7<#?SHS3S<@ES4S38S=S3FAS48SR#s5r>HSRSMSHS4k##$#k##'#k##)#k##+#j##-#1S&DSAS<1s7HD#F;s7H#SH2SB:#'ES4S<#%S<S((s7;S@#C#s7:#Cs7A#'ES4&#%S<S'(s78S?#C#s7?'ES4%#%S<S$9SB7S4$#%S<R(s7JS>#C#s7F#Cs74##Cs79#'ES4'#%S<Q'ES4#s*-%S<O5S4#N%S<M(s7SSy0SB*#/SB*##s7n#s7]#s7o&##s7ps7E#(s7\#(s7[Sj#C#s7%#C%##C.##Cs7M##Cs7=##Cs7>##Cs7=##Cs7@##Cs7A#'ES46#%S<L'ES4#s7$4s#2&D#K3s#4&D#J&D;G&D<s7Z)$#&D<G&D=s7])$#.HS<F-S4S<F$$#$&#$*#$.#$1#$4#$7#$s#-#$s#0#$s#3#$s#:#$s#>#$s#C#$s#I#$s#M#j#$s8:#U#I1S&DS9S31s8<D#F;s8<#SM2S<:#'ESHS3#%S3S((s8/S8#C#s8.#Cs85#'ESH&#%S3S'(s8,S7#C#s83'ESH%#%S3S$9S<7SH$#%S3R(s8>S6#C#s8:#Cs8(##Cs8-#'ESH'#%S3Q'ESH#s*,%S3O5SH#N%S3M(s8GS~0S<*#/S<*##s8b#s8Q#s8c&##s8ds89#(s8P#(s8OS^#C#s7u#C%##C.##Cs8A##Cs81##Cs82##Cs81##Cs84##Cs85#'ESH6#%S3L'ESH#s7t4s#2&D#K3s#4&D#J&D;G&D<s8N)$#&D<G&D=s8Q)$#.HS3F-SHS3F$$#$&#$*#$.#$1#$4#$7#$s#-#$s#0#$s#3#$s#:#$s#>#$s#C#$s#I#$s#M#1S&DS1S41s9.D#F;s9.#S=2S3:#'ESMS4#%S4S((s8}S0#C#s8|#Cs9'#'ESM&#%S4S'(s8zS/#C#s9%'ESM%#%S4S$9S37SM$#%S4R(s90S.#C#s9,#Cs8v##Cs8{#'ESM'#%S4Q'ESM#s)x%S4O5SM#N%S4M(s99Sd0S3*#/S3*##s9T#s9C#s9U&##s9Vs9+#(s9B#(s9AS_#C#s8g#C%##C.##Cs93##Cs9###Cs9$##Cs9###Cs9&##Cs9'#'ESM6#%S4L<SC'ESM$#4s#3&D#K3s#5&D#J&D<G&D=s9A)$#&D=G&D>s9D)$#.HS4F-SMS4F$$#$&#$*#$.#$1#$4#$8#$s#.#$s#1#$s#4#$s#;#$s#?#$s#D#$s#J#$s#N#?SES=SM@ESRS=8SFS=FASR8SS#s8V>HSSSXSESRk##$#k##'#k##)#k##+#j##-#2S4:#'ES=SH#%SHS((s9xS,#C#s9w#Cs9~#'ES=&#%SHS'(s9uS+#C#s9|'ES=%#%SHS$9S47S=$#%SHR(s:+S*#C#s:'#Cs9q##Cs9v#'ES='#%SHQ'ES=#s)~%SHO5S=#N%SHM(s:4SD0S4*#/S4*##s:O#s:>#s:P&##s:Qs:&#(s:=#(s:<Sz#C#s9b#C%##C.##Cs:.##Cs9z##Cs9{##Cs9z##Cs9}##Cs9~#'ES=6#%SHL<T8'ES=$#4s#3&D#K3s#5&D#J&D<G&D=s:<)$#&D=G&D>s:?)$#.HSHF-S=SHF$$#$&#$*#$.#$1#$4#$8#$s#.#$s#1#$s#4#$s#;#$s#?#$s#D#$s#J#1S&DSBSM1s:wD#F;s:w#SE2SM:#'ESES=#%S=S((s:jS9#C#s:i#Cs:p#'ESE&#%S=S'(s:gS8#C#s:n'ESE%#%S=S$9SM7SE$#%S=R(s:yS7#C#s:u#Cs:c##Cs:h#'ESE'#%S=Q'ESE#s(~%S=O5SE#N%S=M(s;&S;0SM*#/SM*##s;A#s;0#s;B&##s;Cs:t#(s;/#(s;.S~#C#s:T#C%##C.##Cs:|##Cs:l##Cs:m##Cs:l##Cs:o##Cs:p#'ESE6#%S=L<S^'ESE$#4s#3&D#K3s#5&D#J&D<G&D=s;.)$#&D=G&D>s;1)$#.HS=F-SES=F$$#$&#$*#$.#$1#$4#$8#$s#.#$s#1#$s#4#$s#;#$s#?#$s#D#$s#J#2S=:#'ESXSR#%SRS((s;YS1#C#s;X#Cs;_#'ESX&#%SRS'(s;VS0#C#s;]'ESX%#%SRS$9S=7SX$#%SRR(s;hS/#C#s;d#Cs;R##Cs;W#'ESX'#%SRQ'ESX#s(y%SRO5SX#N%SRM(s;qS-0S=*#/S=*##s<0#s;{#s<1&##s<2s;c#(s;z#(s;ySd#C#s;C#C%##C.##Cs;k##Cs;[##Cs;\##Cs;[##Cs;^##Cs;_#'ESX6#%SRL<S_'ESX$#4s#3&D#K3s#5&D#J&D<G&D=s;y)$#&D=G&D>s;|)$#.HSRF-SXSRF$$#$&#$*#$.#$1#$4#$8#$s#.#$s#1#$s#4#$s#;#$s#?#$s#D#$s#J#?SQSFSX@ESSSF8SLSFFASS8SU#s;1>HSUSaSQSSk##$#k##'#k##)#k##+#j##-#%SES((s<PS2#C#s<O#Cs<V#'ESF&#%SES'(s<MS,#C#s<T'ESF%#%SES$9SR7SF$#%SER(s<_S+#C#s<[#Cs<I##Cs<N#'ESF'#%SEQ'ESF#s(~%SEO5SF#N%SEM(s<hS)0SR*#/SR*##s='#s<r#s=(&##s=)s<Z#(s<q#(s<pSD#C#s<:#C%##C.##Cs<b##Cs<R##Cs<S##Cs<R##Cs<U##Cs<V#'ESF6#%SEL<Sz'ESF$#2SR4#&D#K3%&D#J&D=G&D>s<q)$#&D>G&D?s<t)$#.HSEF-SFSEF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#$s#<#$s#@#$s#E#2SE:#'ESSSX#%SFS((s=?S<#C#s=>#Cs=E#'ESQ&#%SFS'(s=<S9#C#s=C'ESQ%#%SFS$9SX7SQ$#%SFR(s=NS8#C#s=J#Cs=8##Cs==#'ESQ'#%SFQ'ESQ#s'z%SFO5SQ#N%SFM(s=WS60SX*#/SX*##s=r#s=a#s=s&##s=ts=I#(s=`#(s=_S;#C#s=)#C%##C.##Cs=Q##Cs=A##Cs=B##Cs=A##Cs=D##Cs=E#'ESQ6#%SFL<S~'ESQ$#2SX4#&D#K3%&D#J&D=G&D>s=`)$#&D>G&D?s=c)$#.HSFF-SQSFF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#$s#<#$s#@#$s#E#%SSS((s>+S3#C#s>*#Cs>1#'ESa&#%SSS'(s>(S1#C#s>/'ESa%#%SSS$9SF7Sa$#%SSR(s>:S0#C#s>6#Cs>$##Cs>)#'ESa'#%SSQ'ESa#s't%SSO5Sa#N%SSM(s>CS.0SF*#/SF*##s>^#s>M#s>_&##s>`s>5#(s>L#(s>KS-#C#s=q#C%##C.##Cs>=##Cs>-##Cs>.##Cs>-##Cs>0##Cs>1#'ESa6#%SSL<Sd'ESa$#2SF4#&D#K3%&D#J&D=G&D>s>L)$#&D>G&D?s>O)$#.HSSF-SaSSF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#$s#<#$s#@#$s#E#?SVSLSa@ESUSL8SNSLFASU8S`#s=_>HS`SeSVSUk##$#k##'#k##)#k##+#j##-#%SQS'(s>vS2#C#s>}'ESL%#%SQS$9SS7SL$#%SQR(s?,S,#C#s?(#Cs>r##Cs>w#'ESL'#%SQQ'ESL#s'k%SQO5SL#N%SQM(s?5S*0SS*#/SS*##s?P#s??#s?Q&##s?Rs?'#(s?>#(s?=S)#C#s>c#C%##C.##Cs?/##Cs>{##Cs>|##Cs>{##Cs>~##Cs?##'ESL6#%SQL<SD'ESL$#2SS4#&D#K3%&D#J&D=G&D>s?>)$#&D>G&D?s?A)$#.HSQF-SLSQF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#$s#<#$s#@#%SaS((s?dSH#C#s?c#Cs?j#'ESU&#%SLS'(s?aS<#C#s?h'ESV%#%SLS$9Sa7SV$#%SLR(s?sS9#C#s?o#Cs?]##Cs?b#'ESV'#%SLQ'ESV#s'd%SLO5SV#N%SLM(s?|S70Sa*#/Sa*##s@;#s@*#s@<&##s@=s?n#(s@)#(s@(S6#C#s?N#C%##C.##Cs?v##Cs?f##Cs?g##Cs?f##Cs?i##Cs?j#'ESV6#%SLL<S;'ESV$#2Sa4#&D#K3%&D#J&D=G&D>s@))$#&D>G&D?s@,)$#.HSLF-SVSLF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#$s#<#$s#@#%SUS'(s@GS3#C#s@N'ESe%#%SUS$9SL7Se$#%SUR(s@YS1#C#s@U#Cs@C##Cs@H#'ESe'#%SUQ'ESe#s'[%SUO5Se#N%SUM(s@bS/0SL*#/SL*##s@}#s@l#s@~&##sA#s@T#(s@k#(s@jS.#C#s@4#C%##C.##Cs@\##Cs@L##Cs@M##Cs@L##Cs@O##Cs@P#'ESe6#%SUL<S-'ESe$#2SL4#&D#K3%&D#J&D=G&D>s@k)$#&D>G&D?s@n)$#.HSUF-SeSUF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#$s#<#$s#@#?SYSNSe@ES`SN8STSNFAS`8Sb#s?}>HSbSmSYS`k##$#k##'#k##)#k##+#j##-#%SVS$9SU7SN$#%SVR(sAFS2#C#sAB#CsA0##CsA5#'ESN'#%SVQ'ESN#s'Q%SVO5SN#N%SVM(sAOS+0SU*#/SU*##sAj#sAY#sAk&##sAlsAA#(sAX#(sAWS*#C#s@}#C%##C.##CsAI##CsA9##CsA:##CsA9##CsA<##CsA=#'ESN6#%SVL<S)'ESN$#2SU4#&D#K3%&D#J&D=G&D>sAX)$#&D>G&D?sA[)$#.HSVF-SNSVF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#$s#<#%SeS'(sAuSH#C#sA|'ES`%#%SNS$9Se7SY$#%SNR(sB+S<#C#sB'#CsAq##CsAv#'ESY'#%SNQ'ESY#s'G%SNO5SY#N%SNM(sB4S80Se*#/Se*##sBO#sB>#sBP&##sBQsB&#(sB=#(sB<S7#C#sAb#C%##C.##CsB.##CsAz##CsA{##CsAz##CsA}##CsA~#'ESY6#%SNL<S6'ESY$#2Se4#&D#K3%&D#J&D=G&D>sB=)$#&D>G&D?sB@)$#.HSNF-SYSNF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#$s#<#%S`S$9SN7Sm$#%S`R(sBhS3#C#sBd#CsBR##CsBW#'ESm'#%S`Q'ESm#s'<%S`O5Sm#N%S`M(sBqS00SN*#/SN*##sC0#sB{#sC1&##sC2sBc#(sBz#(sByS/#C#sBC#C%##C.##CsBk##CsB[##CsB\##CsB[##CsB^##CsB_#'ESm6#%S`L<S.'ESm$#2SN4#&D#K3%&D#J&D=G&D>sBz)$#&D>G&D?sB})$#.HS`F-SmS`F$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#$s#<#?SfSTSm@ESbST8SZSTFASb8Sg#sB/>HSgSqSfSbk##$#k##'#k##)#k##+#j##-#%SYR(sCQS4#C#sCM#CsC;##CsC@#'EST'#%SYQ'EST#s'3%SYO5ST#N%SYM(sCZS,0S`*#/S`*##sCu#sCd#sCv&##sCwsCL#(sCc#(sCbS+#C#sC,#C%##C.##CsCT##CsCD##CsCE##CsCD##CsCG##CsCH#'EST6#%SYL<S*'EST$#2S`4#&D#K3%&D#J&D=G&D>sCc)$#&D>G&D?sCf)$#.HSYF-STSYF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#%SmS$9SY7Sb$#%STR(sD1SM#C#sD-#CsCw##CsC|#'ESf'#%STQ'ESf#s'(%STO5Sf#N%STM(sD:S90Sm*#/Sm*##sDU#sDD#sDV&##sDWsD,#(sDC#(sDBS8#C#sCh#C%##C.##CsD4##CsD$##CsD%##CsD$##CsD'##CsD(#'ESf6#%STL<S7'ESf$#2Sm4#&D#K3%&D#J&D=G&D>sDC)$#&D>G&D?sDF)$#.HSTF-SfSTF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#%SbR(sDjS=#C#sDf#CsDT##CsDY#'ESq'#%SbQ'ESq#s&{%SbO5Sq#N%SbM(sDsS10ST*#/ST*##sE2#sD}#sE3&##sE4sDe#(sD|#(sD{S0#C#sDE#C%##C.##CsDm##CsD]##CsD^##CsD]##CsD`##CsDa#'ESq6#%SbL<S/'ESq$#2ST4#&D#K3%&D#J&D=G&D>sD|)$#&D>G&D?sE#)$#.HSbF-SqSbF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#$s#5#?SnSZSq@ESgSZ8ScSZFASg8Sk#sD0>HSkStSnSgk##$#k##'#k##)#k##+#j##-#%SfQ(sEGS4#C#sEN'ESZ%#%SfO5SZ#N%SfM(sEWS20Sb*#/Sb*##sEr#sEa#sEs&##sEtsEI#(sE`#(sE_S,#C#sE)#C%##C.##CsEQ##CsEA##CsEB##CsEA##CsED##CsEE#'ESZ6#%SfL<S+'ESZ$#2Sb4#&D#K3%&D#J&D=G&D>sE`)$#&D>G&D?sEc)$#.HSfF-SZSfF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#%SqR(sF*SE#C#sF&#CsEp##CsEu#'ESg'#%SZQ(sF%SM#C#sF,'ESn%#%SZO5Sn#N%SZM(sF5S<0Sq*#/Sq*##sFP#sF?#sFQ&##sFRsF'#(sF>#(sF=S9#C#sEc#C%##C.##CsF/##CsE{##CsE|##CsE{##CsE~##CsF##'ESn6#%SZL<S8'ESn$#2Sq4#&D#K3%&D#J&D=G&D>sF>)$#&D>G&D?sFA)$#.HSZF-SnSZF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#%SgQ(sFYS=#C#sF`'ESt%#%SgO5St#N%SgM(sFiS30SZ*#/SZ*##sG(#sFs#sG)&##sG*sF[#(sFr#(sFqS1#C#sF;#C%##C.##CsFc##CsFS##CsFT##CsFS##CsFV##CsFW#'ESt6#%SgL<S0'ESt$#2SZ4#&D#K3%&D#J&D=G&D>sFr)$#&D>G&D?sFu)$#.HSgF-StSgF$$#$&#$*#$.#$1#$5#$9#$s#/#$s#2#?SuScSt@ESkSc8SlScFASk8So#sF%>HSoS{SuSkk##$#k##'#k##)#k##+#j##-#%SnO5Sc#N%SnM(sGHS40Sg*#/Sg*##sGc#sGR#sGd&##sGesG:#(sGQ#(sGPS2#C#sFv#C%##C.##CsGB##CsG2##CsG3##CsG2##CsG5##CsG6#'ESc6#%SnL<S,'ESc$#2Sg4#&D#K3%&D#J&D=G&D>sGQ)$#&D>G&D?sGT)$#.HSnF-ScSnF$$#$&#$*#$.#$1#$5#$9#$s#/#%StQ(sGkSE#C#sGr'ESk%#%ScO5Su#N%ScM(sG{SM0St*#/St*##sH:#sH)#sH;&##sH<sGm#(sH(#(sH'S<#C#sGM#C%##C.##CsGu##CsGe##CsGf##CsGe##CsGh##CsGi#'ESu6#%ScL<S9'ESu$#2St4#&D#K3%&D#J&D=G&D>sH()$#&D>G&D?sH+)$#.HScF-SuScF$$#$&#$*#$.#$1#$5#$9#$s#/#%SkO5S{#N%SkM(sHNS=0Sc*#/Sc*##sHi#sHX#sHj&##sHksH@#(sHW#(sHVS3#C#sG|#C%##C.##CsHH##CsH8##CsH9##CsH8##CsH;##CsH<#'ES{6#%SkL<S1'ES{$#2Sc4#&D#K3%&D#J&D=G&D>sHW)$#&D>G&D?sHZ)$#.HSkF-S{SkF$$#$&#$*#$.#$1#$5#$9#$s#/#?SpSlS{@ESoSl8SrSlFASo8Ss#sGe>HSsT#SpSok##$#k##'#k##)#k##+#j##-#%SuM(sI*SR0Sk*#/Sk*##sIE#sI4#sIF&##sIGsHx#(sI3#(sI2S4#C#sHX#C%##C.##CsI$##CsHp##CsHq##CsHp##CsHs##CsHt#'ESl6#%SuL<S2'ESl$#2Sk4#&D#K3%&D#J&D=G&D>sI3)$#&D>G&D?sI6)$#.HSuF-SlSuF$$#$&#$*#$.#$1#$5#$9#%S{O5So#N%SlM(sIXSX0S{*#/S{*##sIs#sIb#sIt&##sIusIJ#(sIa#(sI`SM#C#sI*#C%##C.##CsIR##CsIB##CsIC##CsIB##CsIE##CsIF#'ESp6#%SlL<S<'ESp$#2S{4#&D#K3%&D#J&D=G&D>sIa)$#&D>G&D?sId)$#.HSlF-SpSlF$$#$&#$*#$.#$1#$5#$9#%SoM(sJ(SF0Sl*#/Sl*##sJC#sJ2#sJD&##sJEsIv#(sJ1#(sJ0S=#C#sIV#C%##C.##CsI~##CsIn##CsIo##CsIn##CsIq##CsIr#'ET#6#%SoL<S3'ET#$#2Sl4#&D#K3%&D#J&D=G&D>sJ1)$#&D>G&D?sJ4)$#.HSoF-T#SoF$$#$&#$*#$.#$1#$5#$9#?T,SrT#@ESsSr8S|SrFASs8Sv#sI>>HSvT$T,Ssk##$#k##'#k##)#k##+#j##-#%SpL<S4'ESr$#2So4#&D#K3%&D#J0So&D#G&D$sJT)$#/So&D#G&D$sJX)$#.HSpF-SrSpF$$#$&#$+#$0#$3#$7#%T#M(sJwSQ0Sp*#/Sp*##sK6#sK%#sK7&##sK8sJi#(sK$#(sK#SE#C#sJI#C%##C.##CsJq##CsJa##CsJb##CsJa##CsJd##CsJe#'ESs6#%SrL<SM'ET,$#2T#4#&D#K3%&D#J0T#&D#G&D$sK%)$#/T#&D#G&D$sK))$#.HSrF-T,SrF$$#$&#$+#$0#$3#$7#%SsL<S='ET$$#2Sr4#&D#K3%&D#J0Sr&D#G&D$sK=)$#/Sr&D#G&D$sKA)$#.HSsF-T$SsF$$#$&#$+#$0#$3#$7#?T-S|T$@ESvS|8SwS|FASv8T%#sJJ>HT%T3T-Svk##$#k##'#k##)#k##+#j##-#2Ss4#&D#K3%&D#J0Ss&D#G&D$sK])$#/Ss&D#G&D$sKa)$#.HT,F-S|T,F$$#$&#$+#$0#$3#%T$L<SE'ESv$#2T$4#&D#K3%&D#J0T$&D#G&D$sKt)$#/T$&D#G&D$sKx)$#.HS|F-T-S|F$$#$&#$+#$0#$3#2S|4#&D#K3%&D#J0S|&D#G&D$sL,)$#/S|&D#G&D$sL0)$#.HSvF-T3SvF$$#$&#$+#$0#$3#?T.SwT3@ET%Sw8S}SwFAT%8T&#sK8>HT&T9T.T%k##$#k##'#k##)#k##+#j##-#2Sv3#&D#J0Sv&D#G&D$sLI)$#/Sv&D#G&D$sLM)$#.HT-F-SwT-F$$#$&#$+#$0#2T-4#&D#K2T33#&D#J0T3&D#G&D$sL])$#/T3&D#G&D$sLa)$#.HSwF-T.SwF$$#$&#$+#$0#2Sw3#&D#J0Sw&D#G&D$sLn)$#/Sw&D#G&D$sLr)$#.HT%F-T9T%F$$#$&#$+#$0#?T/S}T9@ET&S}8T'S}FAT&8T0#sKy>HT0T=T/T&k##$#k##'#k##)#k##+#j##-#0T%&D#G&D$sM+)$#/T%&D#G&D$sM/)$#.HT.F-S}T.F$$#$&#$+#2T.3#&D#J0T9&D#G&D$sM;)$#/T9&D#G&D$sM?)$#.HS}F-T/S}F$$#$&#$+#0S}&D#G&D$sMH)$#/S}&D#G&D$sML)$#.HT&F-T=T&F$$#$&#$+#?T(T'T=@ET0T'8T1T'FAT08T2#sLR>HT2TBT(T0k##$#k##'#k##)#k##+#j##-#/T&&D#G&D$sM`)$#.HT/F-T'T/F$$#$&#0T/&D#G&D$sMh)$#/T=&D#G&D$sMl)$#.HT'F-T(T'F$$#$&#/T'&D#G&D$sMt)$#.HT0F-TBT0F$$#$&#?T4T1TB@ET2T18T5T1FAT28T:#sLy>HT:T;T4T2k##$#k##'#k##)#k##+#j##-#.HT(F-T1T(F$$#/T(&D#G&D$sN.)$#.HT1F-T4T1F$$#.HT2F-T;T2F$$#?T6T5T;@ET:T58T>T5FAT:8T)#sM5>HT)T<T6T:k##$#k##'#k##)#k##+#j##-#-T5T4F.HT;F-T6T5F?T)T<T6@ET>T<8PT<FAT>8S##sMC]TUS5PT*T)FS^SjT8I-T*T)F2T)4#&D#K3%&D#J0T)&D#G&D$sNR)$#/T)&D#G&D$sNV)$#.HT*F-PT*F$$#$&#$+#$0#E('SzIE*'SD#E/'S)#E4'S*#E7'S+#$8(1S&DSySO1sO.D#F;sO.#TV2SI:#'ESxSO#%SOS('ESx#sNy%SOS''ESx#sNu%SOS$9SI7Sx$#%SOR'ESx#sNk%SOQ'ESx#sNi%SOO5Sx#N%SOM0SI*#/SI*##sOJ#sO9#sOK&##sOLsN}#(sO8##C#sN[#CsNn##CsO'##CsNs##CsNt##CsNs##CsNv##CsNw#'ESx3#%SOL'ESx#sNZ4s#&&D#K3s#(&D#J&D9G&D:sO4)$#&D:G&D;sO7)$#.HSOF-SxSOF$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#=#$s#A#j#$sOp#+sOq#j#%sOr#+sOs#j#&sOt#+sOu#j#'sOv#+sOw#j#(sOx#+sOy#j#)sOz#+sO{#j#*sO|#+sO}#j#+S&#1S&DS5SI1sP#D#F;sP##TW2SJ:#'ESOSI#%SIS('ESO#sOn%SIS''ESO#sOj%SIS$9SJ7SO$#%SIR'ESO#sO`%SIQ'ESO#sO^%SIO5SO#N%SIM0SJ*#/SJ*##sP?#sP.#sP@&##sPAsOr#(sP-##C#sOP#CsOc##CsOx##CsOh##CsOi##CsOh##CsOk##CsOl#'ESO3#%SIL'ESO#sOO4s#&&D#K3s#(&D#J&D9G&D:sP))$#&D:G&D;sP,)$#.HSIF-SOSIF$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#=#$s#A#j#$sPe#+sPf#j#%sPg#+sPh#j#&sPi#+sPj#j#'sPk#+sPl#j#(sPm#+sPn#j#)sPo#+sPp#j#*sPq#1S&DS#SJ1sPrD#F;sPr#Sx2SK:#'ESISJ#%SJS((sPeT>#C#sPd#CsPk#'ESI&#%SJS''ESI#sP`%SJS$9SK7SI$#%SJR'ESI#sPV%SJQ'ESI#sPT%SJO5SI#N%SJM0SK*#/SK*##sQ5#sQ$#sQ6&##sQ7sPh#(sQ###C#sPF#CsPY##CsPn##CsP^##CsP_##CsP^##CsPa##CsPb#'ESI3#%SJL'ESI#sPE4s#)&D#K3s#+&D#J&D9G&D:sP{)$#&D:G&D;sP~)$#.HSJF-SISJF$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#:#$s#@#$s#D#j#$sQ[#+sQ\#j#%sQ]#+sQ^#j#&sQ_#+sQ`#j#'sQa#+sQb#j#(sQc#+sQd#j#)sQe#1S&DPSK1sQfD#F;sQf#SO2S%:#'ESJSK#%SKS((sQYT<#C#sQX#CsQ_#'ESJ&#%SKS'(sQVT;#C#sQ]'ESJ%#%SKS$9S%7SJ$#%SKR'ESJ#sQL%SKQ'ESJ#sQJ%SKO5SJ#N%SKM0S%*#/S%*##sR+#sQv#sR,&##sR-sQ^#(sQu##C#sQ<#CsQO##CsQd##CsQT##CsQU##CsQT##CsQW##CsQX#'ESJ3#%SKL'ESJ#sQ;4s#+&D#K3s#-&D#J&D9G&D:sQq)$#&D:G&D;sQt)$#.HSKF-SJSKF$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#3#$s#7#$s#<#$s#B#$s#F#j#$sRQ#+sRR#j#%sRS#+sRT#j#&sRU#+sRV#j#'sRW#+sRX#j#(sRY#1S&DT*S%1sRZD#F;sRZ#SI2SG:#'ESKS%#%S%S((sRMT6#C#sRL#CsRS#'ESK&#%S%S'(sRJT4#C#sRQ'ESK%#%S%S$9SG7SK$#%S%R(sR\T(#C#sRX#CsRF##CsRK#'ESK'#%S%Q'ESK#sRB%S%O5SK#N%S%M0SG*#/SG*##sS##sRn#sS$&##sS%sRV#(sRm##C#sR4#CsRG##CsR\##CsRL##CsRM##CsRL##CsRO##CsRP#'ESK3#%S%L'ESK#sR34s#/&D#K3s#1&D#J&D9G&D:sRi)$#&D:G&D;sRl)$#.HS%F-SKS%F$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#0#$s#7#$s#;#$s#@#$s#F#$s#J#j#$sSI#+sSJ#j#%sSK#+sSL#j#&sSM#+sSN#j#'sSO#1S&DT)SG1sSPD#F;sSP#SJ2S5:#'ES%SG#%SGS((sSCT:#C#sSB#CsSI#'ES%&#%SGS'(sS@T2#C#sSG'ES%%#%SGS$9S57S%$#%SGR(sSRT0#C#sSN#CsS<##CsSA#'ES%'#%SGQ(sSMT&#C#sST'ES%%#%SGO5S%#N%SGM0S5*#/S5*##sSw#sSf#sSx&##sSysSN#(sSe##C#sS,#CsS?##CsST##CsSD##CsSE##CsSD##CsSG##CsSH#'ES%3#%SGL'ES%#sS+4s#1&D#K3s#3&D#J&D9G&D:sSa)$#&D:G&D;sSd)$#.HSGF-S%SGF$$#$&#$*#$.#$1#$4#$7#$s#*#$s#-#$s#2#$s#9#$s#=#$s#B#$s#H#$s#L#j#$sTA#+sTB#j#%sTC#+sTD#j#&sTE#1S&DT>S51sTFD#F;sTF#SK2S#:#'ESGS5#%S5S((sT9T5#C#sT8#CsT?#'ESG&#%S5S'(sT6T1#C#sT='ESG%#%S5S$9S#7SG$#%S5R(sTHT'#C#sTD#CsT2##CsT7#'ESG'#%S5Q(sTCS}#C#sTJ'ESG%#%S5O5SG#N%S5M(sTSSw0S#*#/S#*##sTn#sT]#sTo&##sTpsTE#(sT\##C#sT##C,##CsTK##CsT;##CsT<##CsT;##CsT>##CsT?#'ESG4#%S5L'ESG#sS~4s#2&D#K3s#4&D#J&D9G&D:sTX)$#&D:G&D;sT[)$#.HS5F-SGS5F$$#$&#$*#$.#$1#$4#$7#$s#+#$s#.#$s#3#$s#:#$s#>#$s#C#$s#I#$s#M#j#$sU8#+sU9#j#%sU:#1S&DT<S#1sU;D#F;sU;#S%2P:#'ES5S##%S#S((sU.T;#C#sU-#CsU4#'ES5&#%S#S'(sU+TB#C#sU2'ES5%#%S#S$9P7S5$#%S#R(sU=T=#C#sU9#CsU'##CsU,#'ES5'#%S#Q(sU8T9#C#sU?'ES5%#%S#O5S5#N%S#M(sUHT30P*#/P*##sUc#sUR#sUd&##sUesU:#(sUQ#(sUPT$#C#sTv#C%##C.##CsUB##CsU2##CsU3##CsU2##CsU5##CsU6#'ES56#%S#L'ES5#sTu4s#4&D#K3s#6&D#J&D;G&D<sUO)$#&D<G&D=sUR)$#.HS#F-S5S#F$$#$&#$*#$.#$1#$4#$7#$s#-#$s#0#$s#5#$s#<#$s#@#$s#E#$s#K#$s#O#j#$sV/#1S&DT6PKsV<K#K#K#K#H#1sV6D)#;sV6#SG2T*4#L#M#UTX&L#M#UTY)L#M#UTZ,L#M#UT[/L#M#32L#M##C#sV6#C'##C+##C/##C3##C7#'ES#P#KTA=#=#=#=#H#%P#(sVFT4#C#sVE#CsVL#'ES#&#K-=#=#=#H#%P#(sVHT(#C#sVO'ES#%#HsVo%P#9T*7S#$#K9=#=#=#H#%P#(sV`T/#C#sV\#CsVJ##CsVO#'ES#'#=7H#%P#(sV]T.#C#sVd'ES#%#K@=#=#=#H#%P#5S##NKsW4=#K#=#=#=#H#%P#(sVyT-0T**#/T**##sW8#sW'#sW9&##sW:sVk#(sW&#(sW%T,#C#sVK#C%##C.##CsVs##CsVc##CsVd##CsVc##CsVf##CsVg#'ES#6#=s#p=#=#=#H#%P#WT\sWMsW=sW-(sW.#(sW0Sp#C#sW6#C%#'ES#(#&Ds#sK&Ds#eJ&Ds##G&Ds#$sW,)$#&Ds#$G&Ds#%sW/)$#.HPs$#-S#Ps$$$$#$&#$*#$.#$0#$2#$?#$s#<#$s#D#$s#K#$s#W#$s#\#$s#f#$s#r#Qs#tI#UTDTHUT@THVT]DSCUT^DUT_DVT`DTABD#S[#C%S\S:S:SW#S]VTa&SWFTITJVTbIT8&TI#TJm$%#WTcDGSCXTdIT8$#l#,*)#l#-0/#l#.32#j#/D#6IIk#/D#UIS#l#0&$#6PPm#$#,sWf,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#I#%P#%Ps$x6$#6s$W$j#1DI6SCIUTe#j#2D#j#1D#%SCIXTfDDTg#FD#j#3D#j#4D#FDPIIFD#j#1T?#FDs$g`TCT?DDDT+T+11$7s$h#RDDDDDDSh222Sh)PP(7s$i#FD6SDDSi4Si08s$j$77#JDs$lDDs#W#JDs%4DDs#Y#BD%S[#Cs#\S\S:S:SW#S]l#,#s#Ys#Sl#-s#`s#_#l#.s#cs#b#j#/D#%Is$v%Is%=6$#k#/D#l#0'#s#TTs#&s#%2#%Ps#l6#s#)m#%#NS%Ps%EPs#oSjs#V#^T7ES%S5S#Ps%+SnS_S^#Qs$}I#BDs#mS[8Cs#oS\S:S:SW#S]l#,#s#ls#fl#-s#ss#r#l#.s#vs#u#j#/D#6I5k#/D#l#0%#s#e6Ps%/m#$#IsXl%s%2#6#s#<HsY:%s%5#6#s#?FDs%7FD&`TCT?DDDT+T+s#?s#?s#2sXt'#RDDDDDDShs#@s#@s#@Shs#7s%:s%:%+(#SDDSis#ASis#=+(#s#Ds#Ds#0JD*DDs#/#BD#S[s#.Cs$+S\S:S:SW#S]l#,#s$(s#~l#-s$/s$.#l#.s$2s$1#j#/D#%s#-26#s#-k#/D#l#0&#s#~T74/#%s%Is#&6#s#Sm#%#NS%Ps%os%Ls#)Sj>#^T7ES%S5S#s%Ms%JSfS_S^#Qs%BI#JDs%GDDs$<#BDs$=S[#Cs$?S\S:S:SW#S]l#,#s$<s$6l#-s$Cs$B#l#.s$Fs$E#j#/D#%Is%O6I#k#/D#l#0&#s$66Ps%Rm#$#%s%Ts#/6#s#h%s%Vs#.6#s#jFDs%XRDDDDDDShs#is#is#iShs#`s%Ys%Y#s#4s#1s#,SDDSis#jSis#f(&#s#ms#ms#YDD6s#+BD#S[s#VCs$SS\S:S:SW#S]l#,#s$Ps$Jl#-s$Ws$V#l#.s$Zs$Y#j#/D#%6s#:6#s#Uk#/D#l#0&#s$JT31.#%s%gs#$6#s#{m#%#NS%Ps&;s%js#'Sj9#^T7ES%S5S#s%ks%iSYS_S^#JDs%hDDs$b#BDs$cS[#Cs$eS\S:S:SW#S]l#,#s$bs$\l#-s$is$h#l#.s$ls$k#j#/D#%Is%p6I#k#/D#l#0&#s$\=s%W=#H#JD#DD1#BD#S[s#wCs$tS\S:S:SW#S]l#,#s$qs$kl#-s$xs$w#l#.s${s$z#j#/D#%1+6#s#vk#/D#l#0&#s$k%s&&TK6#s$?m#%#NS%Ps&[s&)TKSj5#]ThS%S5S#s&*s&)SVS_S^#Qs%{I#JDs&&DDs%(#BDs%)S[#Cs%+S\S:S:SW#S]l#,#s%(s$~l#-s%/s%.#l#.s%2s%1#j#/D#%Is&.6I#k#/D#l#0&#s$~6Ps&1m#$#%s&3s#w6#s$T%s&5s#v6#s$VFDs&7RDDDDDDShs$Us$Us$UShs$Ls&8s&8#s#|s#ys#tSDDSis$VSis$R(&#s$Ys$Ys$EDD6s#sBD#S[s$BCs%?S\S:S:SW#S]l#,#s%<s%6l#-s%Cs%B#l#.s%Fs%E#j#/D#%6s$&6#s$Ak#/D#l#0&#s%6T31.#%s&Fs#$6#s$gm#%#NS%Ps''s&Is#'Sj9#^T7ES%S5S#s&Js&FSQS_S^#Qs&AI#JDs&FDDs%P#BDs%QS[#Cs%SS\S:S:SW#S]l#,#s%Ps%Jl#-s%Ws%V#l#.s%Zs%Y#j#/D#%Is&N6I#k#/D#l#0&#s%J6Ps&Qm#$#%s&Ss$C6#s$|%s&Us$B6#s$~FDs&WRDDDDDDShs$}s$}s$}Shs$ts&Xs&X#s$Hs$Es$@SDDSis$~Sis$z(&#s%%s%%s$mDD6s$?BD#S[s$jCs%gS\S:S:SW#S]l#,#s%ds%^l#-s%ks%j#l#.s%ns%m#j#/D#%6s$N6#s$ik#/D#l#0&#s%^T31.#%s&fs#$6#s%3m#%#NS%Ps'Os&is#'Sj9#^T7ES%S5S#s&js&hSES_S^#JDs&cDDs%v#BDs%wS[#Cs%yS\S:S:SW#S]l#,#s%vs%pl#-s%}s%|#l#.s&$s&##j#/D#%Is&k6I#k#/D#l#0&#s%pDD-s%-BD#S[s%+Cs&(S\S:S:SW#S]l#,#s&%s%{l#-s&,s&+#l#.s&/s&.#j#/D#%-s'B6#s%*k#/D#l#0&#s%{%s&yTL6#s%Om#%#NS%Ps'ks&|TLSj1#]TiS%S5S#s&}NSHS_S^#Qs&bI#JDs&xDDs&8#BDs&9S[#Cs&;S\S:S:SW#S]l#,#s&8s&2l#-s&?s&>#l#.s&Bs&A#j#/D#%Is'$6I#k#/D#l#0&#s&26Ps''m#$#,s%f,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#,#I#%s'b#6#s&A%s'ds(#6#s&CFDs'fFDs(&`TCT?DDDT+T+s&Cs&Cs&6*s('#RDDDDDDShs&Ds&Ds&DShs&;s'is'i%*s((#SDDSis&ESis&A*(#s&Hs&Hs&4DDs#Qs$bBD#S[s&1Cs'.S\S:S:SW#S]l#,#s'+s'%l#-s'2s'1#l#.s'5s'4#j#/D#%s#Qs(16#s&0k#/D#l#0&#s'%T53.#%s'ws#_6#s&Vm#%#NS%Ps(rs'zs#bSjs#T#^T7ES%S5S#s'{s'hSBS_S^#Qs']I#JDs'eDDs'?#BDs'@S[#Cs'BS\S:S:SW#S]l#,#s'?s'9l#-s'Fs'E#l#.s'Is'H#j#/D#%Is'm6I#k#/D#l#0&#s'96Ps'pm#$#Is'2%s's#6#s&lHs(A%s'v#6#s&oFDs'xFD&`TCT?DDDT+T+s&os&os&bs':'#RDDDDDDShs&ps&ps&pShs&gs'{s'{%+(#SDDSis&qSis&m+(#s&ts&ts&`JD*DD;#BD#S[s&^Cs'[S\S:S:SW#S]l#,#s'Xs'Rl#-s'_s'^#l#.s'bs'a#j#/D#%;26#s&]k#/D#l#0&#s'RT74/#%s(.s#)6#s''m#%#NS%Ps)Cs(1s#,Sj>#^T7ES%S5S#s(2s(-SAS_S^#Es(-s'z#IEs(:s'zs#1#Es(Ws'zs$9#Es(_s'zs$V#Es(fs'zs%##Es(rs'zs%L#Es(ws'zs%m#Es)%s'zs&:#Es)1s'zs&e#Es)Ls'zSu#1s]&Ds)UF;s]&#SG:s)N'ES#P#%PS('ES##s).%PS''ES##s)'%PS$7S##s)%%PR'ES##s(x%PQ'ES##s(t%PO5S##N%PM'ES##s(U%PL<Sp'ES#$#.HPF-S#PF$$#$s(G#$s(K#$s(O#$s(Q#$*#$.#$1#$4#$7#$:#$=#$@#$s###$s#&#m#s#)#Os]Ns)}Sp#Os]Os*sT,#Os]Ps+iT-#Os]Qs,`T.#Os]Rs-WT/#Os]Ss.LT(#Os]Ts/AT4#OS&s05T6#l#5s1,s1+#l#6s1Fs1E#j#7s1H#j#8s1K#j#9s1M#j#:s1O#j#;s1Q#j#<s1S#V#SCIj##s1V#j##s1e#Gs1fs1es1Y#Ij#=s1h#j#>s1l#V#SCIj##s1r#j##s2)#Gs2*s2's1w#Ij#=s2/#j#?s28#V#SCIj##s2>#j##s2[#Gs2\s2Ts2H#Ij#=s2a#j#@s2o#V#SCIj##s2t#j##s3?#Gs3@s33s3'#Ij#=s3D#j#As3V#V#SCIj##s3[#j##s4-#Gs4.s3zs3n#Ij#=s42#j#Bs4G#V#SCIj##s4L#j##s5%#Gs5&s4ns4b#Ij#=s5*#j#Cs5C#V#SCIj##s5Z#j##s69#Gs6:s6$s5t#Ij#=s6P#j#Ds6}#V#SCIj##s7%#j##s8.#Gs8/s7_s7S#Ij#=s82#j#Es8b#V#SCIj##s8h#j##s9w#Gs9xs9Is9=#Ij#=s9}#j#Fs:V#V#SCIj##s:^#j##s;u#Gs;vs;Ds;8#Ij#=s;}#j#Gs<[#V#SCIj##s<`#j##s>'#Gs>(s=Ks=?#Ij#=s>,#j#Hs>j#V#SCIj##s>p#j##s@?#Gs@@s?_s?S#Ij#=s@E#j#IsA,#V#SCIj##sA3#j##sBh#GsBisB'sAw#Ij#=sBo#j#JsC\#V#SCIj##sCa#j##sEE#GsEFsD[sDO#Ij#=sEJ#j#KsF:#V#SCIj##sF?#j##sH*#GsH+sG<sG0#Ij#=sH/#j#$s^[#V#SCIj##sI$#j#1s^^#Ps^_sJ&sIv#Ij#=sJv#j#%s^a#V#SCIj##sKk#j#1s^d#Ps^esLmsLa#Ij#=sMa#j#&s^g#V#SCIj##sNW#j#1s^j#Ps^ksOZsON#Ij#=sPQ#j#'s^m#V#SCIj##sQI#j#1s^p#Ps^qsRNsRB#Ij#=sSE#j#(s^s#V#SCIj##sT;#j#1s^v#Ps^wsU>sU2#Ij#=sV3#j#)s^y#V#SCIj##sW)#j#1s^|#Ps^}sX,sW|#Ij#=sX}#j#*s_##V#SCIj##sYr#j#1s_&#Ps_'sZtsZh#Ij#=s[h#j#+S&#V#SCIj##s\_#j#1S&#PS&s]ds]W#Ij#=s_/#j#LTj#j#MD#j#Ns_3#j#3Tk#j#Os_A#j#Ps_C##"). Qed.

Lemma AImplBlock_transport : forall W LB m m' b I,
  AImplBlock LB m b I -> munch W m m' -> wmono bsegs m m' -> disjoint_from W b SZ_SPCI_IMPL ->
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
  AStateBlock LB m b ioc implb S ds -> munch W m m' -> wmono bsegs m m' -> disjoint_from W b SZ_SPCI_STATE ->
  (st_fb S <> FB_empty -> disjoint_from W (fb_begin (st_fb S)) (fb_cap (st_fb S))) ->
  disjoint_from W (sh b) (nsh SZ_SPCI_STATE) ->
  (st_fb S <> FB_empty -> disjoint_from W (sh (fb_begin (st_fb S))) (nsh (fb_cap (st_fb S)))) -> AStateBlock LB m' b ioc implb S ds.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.ivl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.block); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.statev); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AStateBlock); constr:(HCEIL); constr:(@kc__3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsIface.bptr); constr:(@Corelib.Init.Logic.ex); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_SPCI_STATE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPres.rblock_range); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SpcHdrCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.st_hdr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.spc_ok); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.spc_vptr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AVP_SPCI_STATE); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_ST_EXEC); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AnyExecCells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_ST_WP_PX); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.wz); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_SPC_STORAGE); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.APMutex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_ST_MUTEX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.st_lk); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AFlatBuf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_ST_FB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.st_fb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.APCond); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_ST_CV); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.O_ST_OP); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.C4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.st_code); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.st_nread); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.st_nread_bytes); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.u64max); constr:(@Corelib.Init.Logic.or); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.STREAM_OK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.STREAM_EOF); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.addressable); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.munch); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.wmono); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.disjoint_from); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fbv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.FB_empty); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fb_begin); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.fb_cap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.nsh); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.addressable_transport); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.ex_intro); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.spc_use); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.spc_weak); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.spc_init); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_OBJECT_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_TARGET_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.AT_ANYEX_PROP_FNS); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Frame.rw_cells_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.KIT.disjoint_from_sub); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.micromega.ZifyClasses.inj); constr:(@Stdlib.micromega.ZifyInst.Inj_Z_Z); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Corelib.Init.Datatypes.nat); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.KIT.APMutex_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_PMUTEX); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.KIT.AFlatBuf_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_FB); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.KIT.APCond_transport); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.SZ_PCOND)|] [|@j4; @j16; @j7; @p; @__ff; @__varmap; @__wit; @__x1; @__arith; @x; @y; @m; @n; @E; @AD'; @DSF; @DS; @DF; @D; @WM; @MU; @AD; @E3; @H; @E2; @E1; @CO; @PC; @FB; @PM; @CW; @CE; @EV; @OK; @CH; @RB; @IN; @ds; @S; @implb; @ioc; @b; @m'; @LB; @W|] "#Q|$$%G$K$0$>$X$;$3##$c$d$Y$W$T#x$Q$n$o#y#$$I$N#/#3$G#1#0#5$D#4#9#2#7#8#|$5#6#;%-#=#.#?#A#z#C#E#G#:#>#I#K#M#-#B#,#*#)#N#+#<#F#J#Q#{#O#S#@#D%%#P#U#H#R#W#V#Y#]#_%.#%#L#[#w%1%,%2#(#T#Z#v#X#a#^#\#c#`#g#k#e#d#i#o#}#b#h#m#q#u#t$E$e#l#'#&#r%$#f#n#s#p#j%A$'%&%@%=%;%:%#$w$4$.$O$,$+$9$##~%'%6%7%E%G%I$($)$/$^$a$g$u$x$y${$z$|$}$~%(%)%+%0%3%8%9%4%<%>%?%D%F%H$1$*$7$J$M$L$B$=$f$U$l$]$i$`$_$[$b$Z$V$S$P$R$:$m$p$q$r$\$H$@$C$-$A$6$?$<$8$s$2$j$k$v%/%*%B$t$F%5%C$hU$s%$t&$2%$u$$v$$w&$x'$3%$y%$z$${&$|$$}&$~$%#$%$$%%%%&$%'&%()%)&%*$%+'%,$%-$%.$%/$%0%%1&%2$%3$%4$%5$%6%%7%%8&%9&%:$%;+%<&%=&%>'%?'%@*%A&%B(%C$%D%%E%%F$UT/TEUT/TFBT8B#B#B#B#B#UT:#UT;#UT:(UT;#UTG#k##&#UT/%IHSHSIT%T&S`S$IVT<S4DVT<#D9S4DT&SG9%D#GG%#S'FHSGG@SIE#S`)ES9SG#C%A&(D#S-Q8%SG#%#S)?#SKS$)ES9$#%&S%%SHS&&#'#&SH'#UT9C$C$#$C'#)ES9+#%0P8SI7S9$#%3N,SI6HS'S9$#Sg%6M5S9#F%8L&F'#2SI&#4#.TH.#.#.#>#I1SI&#'#0SI&#'#&TI'#$C#A$C$#$C5#$C6#$C)#$C-#$C9#$C2#$C8#$C<#)ES9?#(D=J(D>K3$#*F8Qs#UTT8T#T#T#T#Q#VTJ)#+A##,#*F@+A&#$#/S9SGG#$##(##4##8##s#7##s#:##s#>##s#B##s#M##s#S##s#V##s#X##s#\##s#^#j#$s#e#Ds#f#j#%s#g#Ds#h#j#&s#i#Ds#j#j#'S4#DS4#JSESKSHKESGSK-S'SKG(Qs#OR:#,SH;#<$-S*$#k##'#=SEHG-S*$#,SK(Q#R:#,SG;#=#<%H#-S(%#k##)#IHS0S+S'S9SESGSKk##$#k##/#k##3#k##;#k##=#k##?#j##A#9S4DT&SE9s$/D#GGs$/#S+FHSEG@SHE#S`)ES'SE#C%A&(D#S-%SEs$,%#S)?#SGS$)ES'$#%&S%%SKS&&#'#&SK'#$C#s$+$C&#)ES'*#%/P8SH7S'$#%2N6HS+S'#s#7SI%4M5S'#F%6L2SH&#4#1SH&#'#0SH&#'#$C#s#y$C'#$Cs$3#$Cs$,#$C-#$Cs$6#)ES'2#(D2J(D3K3$#*F2+3s#q#$#*F2+3s#t#$#/S'SEG#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#j#$s$w#Ds$x#j#%s$y#Ds$z#j#&s${#Ds$|#j#'S4#U#I9S4DT&S99s$~D#GGs$~#S*FHS9G@SKE#S`)ES+S9#C%A&(D#S-%S9s${%#S)?#SES$)ES+$#%&S%%SGS&&#'#&SG'#$C#s$z$C&#)ES+*#%/P8SK7S+$#%2N6HS*S+#s#~SH%4M5S+#F%6L2SK&#4#1SK&#'#0SK&#'#$C#s$l$C'#$Cs%&#$Cs${#$C-#$Cs%)#)ES+2#(D2J(D3K3$#*F2+3s$d#$#*F2+3s$g#$#/S+S9G#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#j#$s%j#Ds%k#j#%s%l#Ds%m#j#&s%n#Ds%o#9S4DT%S'9s%oD#GGs%o#S0FHS'G@SGE#S`)ES*S'#C%A&(D#S-%S's%l%#S)?#S9S$)ES*$#%&S%%SES&&#'#&SE'#$C#s%k$C&#)ES**#%/P8SG7S*$#%2N6HS0S*#s$lSK%4M5S*#F%6L2SG&#4#1SG&#'#0SG&#'#$C#s%]$C'#$Cs%s#$Cs%l#$C-#$Cs%v#)ES*2#(D2J(D3K3$#*F2+3s%U#$#*F2+3s%X#$#/S*S'G#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#j#$s&[#Ds&\#j#%s&]#Ds&^#j#&s&_#Ds&`#JS*S'S9KES+S'-S(S'G,SE(Q#R:#,S9;#<$-S,$#k##'#=S*-S,#s%S,S'(Q#R:#,S+;#=#<%H#-S1%#k##)#IHS5S.S(S0S*S+S'k##$#k##/#k##2#k##;#k##=#k##?#j##A#9S4DSgS+9s'#D#GGs'##S(FHS+G@SEE#S`)ES0S+#C%A&(D#S-%S+s&|%#S)?#S'S$)ES0$#%&S%%S9S&&#'#&S9'#$C#s&{$C&#)ES0*#%/P8SE7S0$#%2N6HS(S0#s#9SG%4M5S0#F%6L2SE&#4#1SE&#'#0SE&#'#$C#s&m$C'#$Cs''#$Cs&|#$C-#$Cs'*#)ES02#(D2J(D3K3$#*F2+3s&e#$#*F2+3s&h#$#/S0S+G#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#j#$s'k#Ds'l#j#%s'm#Ds'n#j#&s'o#U#I9S4DSIS*9s'pD#GGs'p#S.FHS*G@S9E#S`)ES(S*#C%A&(D#S-%S*s'm%#S)?#S+S$)ES($#%&S%%S'S&&#'#&S''#$C#s'l$C&#)ES(*#%/P8S97S($#%2N6HS.S(#s$'SE%4M5S(#F%6L2S9&#4#1S9&#'#0S9&#'#$C#s'^$C'#$Cs't#$Cs'm#$C-#$Cs'w#)ES(2#(D2J(D3K3$#*F2+3s'V#$#*F2+3s'Y#$#/S(S*G#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#j#$s(\#Ds(]#j#%s(^#Ds(_#9S4DSHS09s(_D#GGs(_#S,FHS0G@S'E#T&)ES.S0#C%A&(D#S-%S0s(\%#S)?#S*S$)ES.$#%&S%%S+S&&#'#&S+'#$C#s([$C&#)ES.*#%/P8S'7S.$#%2N6HS,S.#s$kS9%4M5S.#F%6L2S'&#4#1S'&#'#0S'&#'#$C#s(M$C'#$Cs(c#$Cs(\#$C-#$Cs(f#)ES.2#(D2J(D3K3$#*F2+3s(E#$#*F2+3s(H#$#/S.S0G#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#j#$s)K#Ds)L#j#%s)M#Ds)N#JS,S(S0KES.S(-S1S(G,S*(Q#R:#,S0;#<$-S/$#k##'#=S,-S/#s(A,S((Q#R:#,S.;#=#<%H#-S6%#k##)#IHS@S2S1S5S,S.S(k##$#k##/#k##2#k##;#k##=#k##?#j##A#9S4DSKS(9s)mD#GGs)m#S5FHS(G@S+E#T%)ES,S(#C%A&(D#S-%S(s)j%#S)?#S0S$)ES,$#%&S%%S*S&&#'#&S*'#$C#s)i$C&#)ES,*#%/P8S+7S,$#%2N6HS5S,#s%vS'%4M5S,#F%6L2S+&#4#1S+&#'#0S+&#'#$C#s)[$C'#$Cs)q#$Cs)j#$C-#$Cs)t#)ES,2#(D2J(D3K3$#*F2+3s)S#$#*F2+3s)V#$#/S,S(G#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#j#$s*Y#Ds*Z#j#%s*[#U#I9S4DSGS.9s*\D#GGs*\#S1FHS.G@S*E#Sg)ES5S.#C%A&(D#S-%S.s*Y%#S)?#S(S$)ES5$#%&S%%S0S&&#'#&S0'#$C#s*X$C&#)ES5*#%/P8S*7S5$#%2N6HS1S5#s$(S+%4M5S5#F%6L2S*&#4#1S*&#'#0S*&#'#$C#s*J$C'#$Cs*`#$Cs*Y#$C-#$Cs*c#)ES52#(D2J(D3K3$#*F2+3s*B#$#*F2+3s*E#$#/S5S.G#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#j#$s+H#Ds+I#9S4DSES,9s+ID#GGs+I#S2FHS,G@S0E#SI)ES1S,#C%A&(D#S-%S,s+F%#S)?#S.S`)ES1$#%&S%%S(S&&#'#&S('#$C#s+E$C&#)ES1*#%/P8S07S1$#%2N6HS2S1#s$nS*%4M5S1#F%6L2S0&#4#1S0&#'#0S0&#'#$C#s+7$C'#$Cs+M#$Cs+F#$C-#$Cs+P#)ES12#(D2J(D3K3$#*F2+3s+/#$#*F2+3s+2#$#/S1S,G#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#j#$s,5#Ds,6#JS/S1S5KES2S1-S6S1G,S,(Q#R:#,S5;#<$-S8$#k##'#=S/-S8#s+),S1(Q#R:#,S2;#=#<%H#-S:%#k##)#IHSASLS6S@S/S2S1k##$#k##/#k##2#k##;#k##=#k##?#j##A#9S4DS9S59s,UD#GGs,U#S/FHS5G@S(E#SH)ES2S5#C%A&(D#S-%S5s,R%#S)?#S,T&)ES2$#%&S%%S.S&&#'#&S.'#$C#s,Q$C&#)ES2*#%/P8S(7S2$#%2N6HS/S2#s%sS0%4M5S2#F%6L2S(&#4#1S(&#'#0S(&#'#$C#s,C$C'#$Cs,Y#$Cs,R#$C-#$Cs,\#)ES22#(D2J(D3K3$#*F2+3s,;#$#*F2+3s,>#$#/S2S5G#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#j#$s-A#U#I9S4DS'S19s-BD#GGs-B#S@FHS1G@S.E#SK)ES/S1#C%A&(D#S-%S1s-?%#S)?#S5T%)ES/$#%&S%%S,S&&#'#&S,'#$C#s->$C&#)ES/*#%/P8S.7S/$#%2N6HS@S/#s&]S(%4M5S/#F%6L2S.&#4#1S.&#'#0S.&#'#$C#s-0$C'#$Cs-F#$Cs-?#$C-#$Cs-I#)ES/2#(D2J(D3K3$#*F2+3s-(#$#*F2+3s-+#$#/S/S1G#$##(##,##0##B##s#%##s#(##s#,##s#6##s#;##s#>##s#@##s#D##s#F#9S4DS+S29s.-D#GGs.-#S6FHS2G@S,E#SG)ES@S2#C%A&(D#S-%S2s.*%#S)?#S1Sg)ES@$#%&S%%S5S&&#'#&S5'#$C#s.)$C&#)ES@*#%/P8S,7S@$#%2N6HS6S@#s$mS.%4M5S@#F%6L2S,&#4#>s-~S$1S,&#'#0S,&#'#$C#s-x$C'#$Cs.2#$C,#$C.#$Cs.5#)ES@3#(D3J(D4K3$#*F2+3s-p#$#*F2+3s-s#$#/S@S2G#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<##s#?##s#A##s#E##s#G#JS8S6S@KESLS6-S:S6G,S/(Q#R:#,S@;#<$-S;$#k##'#=S8-S;#s-h,S6(Q#R:#,SL;#=#<%H#-S=%#k##)#IHSFSSS:SAS8SLS6k##$#k##/#k##2#k##;#k##=#k##?#j##A#FHS/G@S5E#SE)ES6S/#C%A&(D#S-%S/s/2%#S)?#S2SI)ES6$#%&S%%S1S&&#'#&S1'#$C#s/1$C&#)ES6*#%/P8S57S6$#%2N6HSLS6#s%rS,%4M5S6#F%6L2S5&#4#>s/*S`1S5&#'#0S5&#'#$C#s/$$C'#$Cs/:#$C,#$C.#$Cs/=#)ES63#(D3J(D4K3$#*F2+3s.x#$#*F2+3s.{#$#/S6S/G#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<##s#?##s#A##s#E#9S4DS0S@9s/|D#GGs/|#S8FHS6G@S2E#S')ES8S6#C%A&(D#S-%S6s/y%#S)?#S@SK)ES8$#%&S%%S/S&&#'#&S/'#$C#s/x$C&#)ES8*#%/P8S27S8$#%2N6HSAS8#s&SS1%4M5S8#F%6L2S2&#4#>s/qT%1S2&#'#0S2&#'#$C#s/k$C'#$Cs0%#$C,#$C.#$Cs0(#)ES83#(D3J(D4K3$#*F2+3s/c#$#*F2+3s/f#$#/S8S6G#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<##s#?##s#A##s#E#FHSLG@S/E#S+)ESASL#C%A&(D#S-%SLs0a%#S)?#S6SG)ESA$#%&S%%S@S&&#'#&S@'#$C#s0`$C&#)ESA*#%/P8S/7SA$#%2N6HS:SA#s$eS2%4M5SA#F%6L2S/&#4#>s0YSg1S/&#'#0S/&#'#$C#s0S$C'#$Cs0i#$C,#$C.#$Cs0l#)ESA3#(D3J(D4K3$#*F2+3s0K#$#*F2+3s0N#$#/SASLG#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<##s#?##s#A##s#E#JS;S:SAKESSS:-S=S:G,S8(Q#R:#,SA;#<$-S>$#k##'#=S;-S>#s0B,S:(Q#R:#,SS;#=#<%H#-S?%#k##)#IHSMSTS=SFS;SSS:k##$#k##/#k##2#k##;#k##=#k##?#j##A#@S@E#S*)ES:S8#C%A&(D#S-%S8s1g%#S)?#SLSE)ES:$#%&S%%S6S&&#'#&S6'#$C#s1f$C&#)ES:*#%/P8S@7S:$#%2N6HSSS:#s%hS/%4M5S:#F%6L2S@&#4#>s1_SI1S@&#'#0S@&#'#$C#s1Y$C'#$Cs1o#$C,#$C.#$Cs1r#)ES:3#(D3J(D4K3$#*F2+3s1Q#$#*F2+3s1T#$#/S:S8G#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<##s#?##s#A#FHSAG@SLE#S()ES;S:#C%A&(D#S-%S:s2N%#S)?#SAS')ES;$#%&S%%S8S&&#'#&S8'#$C#s2M$C&#)ES;*#%/P8SL7S;$#%2N6HSFS;#s&ES6%4M5S;#F%6L2SL&#4#>s2FSK1SL&#'#0SL&#'#$C#s2@$C'#$Cs2V#$C,#$C.#$Cs2Y#)ES;3#(D3J(D4K3$#*F2+3s28#$#*F2+3s2;#$#/S;S:G#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<##s#?##s#A#@S8E#S.)ESFSS#C%A&(D#S-%SSs34%#S)?#S:S+)ESF$#%&S%%SAS&&#'#&SA'#$C#s33$C&#)ESF*#%/P8S87SF$#%2N6HS=SF#s$^SL%4M5SF#F%6L2S8&#4#>s3,SG1S8&#'#0S8&#'#$C#s3&$C'#$Cs3<#$C,#$C.#$Cs3?#)ESF3#(D3J(D4K3$#*F2+3s2z#$#*F2+3s2}#$#/SFSSG#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<##s#?##s#A#JS>S=SFKESTS=-S?S=G,S;(Q#R:#,SF;#<$-SB$#k##'#=S>-SB#s2p,S=(Q#R:#,ST;#=#<%H#-SC%#k##)#IHSNSXS?SMS>STS=k##$#k##/#k##2#k##;#k##=#k##?#j##A#@SAC#A$(D#S-%S;s47%#S)?#SSS*)ES=$#%&S%%S:S&&#'#&S:'#$C#s46$C&#)ES=*#%/P8SA7S=$#%2N6HSTS=#s%^S8%4M5S=#F%6L2SA&#4#>s4/SE1SA&#'#0SA&#'#$C#s4)$C'#$Cs4?#$C,#$C.#$Cs4B#)ES=3#(D3J(D4K3$#*F2+3s3}#$#*F2+3s4$#$#/S=S;G#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<##s#?#@S:E#S5)ESTSF#@SSC#A$(D#S-%S=s4y%#S)?#SFS()ES>$#%&S%%S;S&&#'#&S;'#$C#s4x$C&#)ES>*#%/P8SS7S>$#%2N6HSMS>#s&:S:%4M5S>#F%6L2SS&#4#>s4qS'1SS&#'#0SS&#'#$C#s4k$C'#$Cs5%#$C,#$C.#$Cs5(#)ES>3#(D3J(D4K3$#*F2+3s4c#$#*F2+3s4f#$#/S>S=G#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<##s#?#@S;C#A$(D#S-%STs5\%#S)?#S=S.)ESM$#%&S%%SFS&&#'#&SF'#$C#s5[$C&#)ESM*#%/P8S;7SM$#%2N6HS?SM#s$XSS%4M5SM#F%6L2S;&#4#>s5TS+1S;&#'#0S;&#'#$C#s5N$C'#$Cs5d#$C,#$C.#$Cs5g#)ESM3#(D3J(D4K3$#*F2+3s5F#$#*F2+3s5I#$#/SMSTG#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<##s#?#JSBS?SMKESXS?-SCS?G,S>(Q#R:#,SM;#<$-SD$#k##'#=SB-SD#s5;,S?(Q#R:#,SX;#=#<%H#-SQ%#k##)#IHSJSaSCSNSBSXS?k##$#k##/#k##2#k##;#k##=#k##?#j##A#@SFA#(D#S-%S>s6]%#S)?#STS,)ES?$#%&S%%S=S&&#'#&S='#$C#s6\$C&#)ES?*#%/P8SF7S?$#%2N6HSXS?#s%VS;%4M5S?#F%6L2SF&#4#>s6US*1SF&#'#0SF&#'#$C#s6O$C'#$Cs6e#$C,#$C.#$Cs6h#)ES?3#(D3J(D4K3$#*F2+3s6G#$#*F2+3s6J#$#/S?S>G#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<#@S=C#@STA#(D#S-%S?s7@%#S)?#SMS1)ESB$#%&S%%S>S&&#'#&S>'#$C#s7?$C&#)ESB*#%/P8ST7SB$#%2N6HSNSB#s&/S=%4M5SB#F%6L2ST&#4#>s78S(1ST&#'#0ST&#'#$C#s72$C'#$Cs7H#$C,#$C.#$Cs7K#)ESB3#(D3J(D4K3$#*F2+3s7*#$#*F2+3s7-#$#/SBS?G#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<#@S>A#(D#S-%SXs7}%#S)?#S?S2)ESN$#%&S%%SMS&&#'#&SM'#$C#s7|$C&#)ESN*#%/P8S>7SN$#%2N6HSCSN#s$RST%4M5SN#F%6L2S>&#4#>s7uS.1S>&#'#0S>&#'#$C#s7o$C'#$Cs8)#$C,#$C.#$Cs8,#)ESN3#(D3J(D4K3$#*F2+3s7g#$#*F2+3s7j#$#/SNSXG#$##(##,##0##s####s#&##s#)##s#-##s#7##s#<#JSDSCSNKESaSC-SQSCG,SB(Q#R:#,SN;#<$-SO$#k##'#=SD-SO#s7[,SC(Q#R:#,Sa;#=#<%H#-SR%#k##)#IHSYSVSQSJSDSaSCk##$#k##/#k##2#k##;#k##=#k##?#j##A#%SBs8z%#S)?#SXS/)ESC$#%&S%%S?S&&#'#&S?'#$C#s8y$C&#)ESC*#%/P8SM7SC$#%2N6HSaSC#s%LS>%4M5SC#F%6L2SM&#4#>s8rS,1SM&#'#0SM&#'#$C#s8l$C'#$Cs9&#$C,#$C.#$Cs9)#)ESC3#(D3J(D4K3$#*F2+3s8d#$#*F2+3s8g#$#/SCSBG#$##(##,##0##s####s#&##s#)##s#-##s#7#@S?A#(D#S-%SCs9Z%#S)?#SNS6)ESD$#%&S%%SBS&&#'#&SB'#$C#s9Y$C&#)ESD*#%/P8SX7SD$#%2N6HSJSD#s%~S?%4M5SD#F%6L2SX&#4#>s9RS11SX&#'#0SX&#'#$C#s9L$C'#$Cs9b#$C,#$C.#$Cs9e#)ESD3#(D3J(D4K3$#*F2+3s9D#$#*F2+3s9G#$#/SDSCG#$##(##,##0##s####s#&##s#)##s#-##s#7#%Sas:7%#S)?#SCSL)ESJ$#%&S%%SNS&&#'#&SN'#$C#s:6$C&#)ESJ*#%/P8SB7SJ$#%2N6HSQSJ#s$HSX%4M5SJ#F%6L2SB&#4#>s:/S21SB&#'#0SB&#'#$C#s:)$C'#$Cs:?#$C,#$C.#$Cs:B#)ESJ3#(D3J(D4K3$#*F2+3s9}#$#*F2+3s:$#$#/SJSaG#$##(##,##0##s####s#&##s#)##s#-##s#7#JSOSQSJKESVSQ-SRSQG,SD(Q#R:#,SJ;#<$-SW$#k##'#=SO-SW#s9p,SQ(Q#R:#,SV;#=#<%H#-SZ%#k##)#IHS[ShSRSYSOSVSQk##$#k##/#k##2#k##;#k##=#k##?#j##A#%SDs;3%#S%%SCS&&#'#&SC'#$C#s;/$C&#)ESQ*#%,P8SN7SQ$#%/N6HSVSQ#s%>SB%1M5SQ#F%3L2SN&#4#>s;(S/1SN&#'#0SN&#'#$C#s:~$C'#$Cs;8#$C,#$C.#$Cs;;#)ESQ3#(D3J(D4K3$#*F2+3s:v#$#*F2+3s:y#$#/SQSDG#$##(##,##0##s####s#&##s#)##s#-#%SJs;h%#S)?#SDSA)ESV$#%SQs;l%#S%%SDS&&#'#&SD'#$C#s;h$C&#)ESO*#%,P8Sa7SO$#%/N6HSYSO#s%mSC%1M5SO#F%3L2Sa&#4#>s;aS61Sa&#'#0Sa&#'#$C#s;[$C'#$Cs;q#$C,#$C.#$Cs;t#)ESO3#(D3J(D4K3$#*F2+3s;S#$#*F2+3s;V#$#/SOSQG#$##(##,##0##s####s#&##s#)##s#-#%SVs<E%#S%%SJS&&#'#&SJ'#$C#s<A$C&#)ESY*#%,P8SD7SY$#%/N6HSRSY#s$>Sa%1M5SY#F%3L2SD&#4#>s<:SL1SD&#'#0SD&#'#$C#s<4$C'#$Cs<J#$C,#$C.#$Cs<M#)ESY3#(D3J(D4K3$#*F2+3s<,#$#*F2+3s</#$#/SYSVG#$##(##,##0##s####s#&##s#)##s#-#JSWSRSYKEShSR-SZSRG,SO(Q#R:#,SY;#<$-S\$#k##'#=SW-S\#s;z,SR(Q#R:#,Sh;#=#<%H#-Sb%#k##)#IHSiSkSZS[SWShSRk##$#k##/#k##2#k##;#k##=#k##?#j##A#%SOs==%#P8SJ7SR$#%&N6HShSR#s%*SD%(M5SR#F%*L2SJ&#4#>s=)S81SJ&#'#0SJ&#'#$C#s=#$C'#$Cs=9#$C,#$C.#$Cs=<#)ESR3#(D3J(D4K3$#*F2+3s<w#$#*F2+3s<z#$#/SRSOG#$##(##,##0##s####s#&##s#)#%SYs=h%#S%%SVS&&#'#&SV'#$C#s=d$C&#)ESh*#%SRs=r%#P8SV7SW$#%&N6HS[SW#s%USQ%(M5SW#F%*L2SV&#4#>s=^S:1SV&#'#0SV&#'#$C#s=X$C'#$Cs=n#$C,#$C.#$Cs=q#)ESW3#(D3J(D4K3$#*F2+3s=P#$#*F2+3s=S#$#/SWSRG#$##(##,##0##s####s#&##s#)#%Shs>A%#P8SO7S[$#%&N6HSZS[#s$'SV%(M5S[#F%*L2SO&#4#>s>-SS1SO&#'#0SO&#'#$C#s>'$C'#$Cs>=#$C,#$C.#$Cs>@#)ES[3#(D3J(D4K3$#*F2+3s={#$#*F2+3s=~#$#/S[ShG#$##(##,##0##s####s#&##s#)#JS\SZS[KESkSZ-SbSZG,SW(Q#R:#,S[;#<$-S]$#k##'#=S\-S]#s=l,SZ(Q#R:#,Sk;#=#<%H#-S^%#k##)#IHSmSnSbSiS\SkSZk##$#k##/#k##2#k##;#k##=#k##?#j##A#%SWs?/%#N6HSkSZ#s$kSO%%M5SZ#F%'L2SY&#4#>s>tS;1SY&#'#0SY&#'#$C#s>n$C'#$Cs?(#$C,#$C.#$Cs?+#)ESZ3#(D3J(D4K3$#*F2+3s>f#$#*F2+3s>i#$#/SZSWG#$##(##,##0##s####s#&#%S[s?V%#P8SR7Sk$#%SZs?Z%#N6HSiS\#s%0SR%%M5S\#F%'L2Sh&#4#>s?CS=1Sh&#'#0Sh&#'#$C#s?=$C'#$Cs?S#$C,#$C.#$Cs?V#)ES\3#(D3J(D4K3$#*F2+3s?5#$#*F2+3s?8#$#/S\SZG#$##(##,##0##s####s#&#%Sks@%%#N6HSbSi#s#rSh%%M5Si#F%'L2SW&#4#>s?jST1SW&#'#0SW&#'#$C#s?d$C'#$Cs?z#$C,#$C.#$Cs?}#)ESi3#(D3J(D4K3$#*F2+3s?\#$#*F2+3s?_#$#/SiSkG#$##(##,##0##s####s#&#JS]SbSiKESnSb-S^SbG,S\(Q#R:#,Si;#<$-Sl$#k##'#=S]-Sl#s?L,Sb(Q#R:#,Sn;#=#<%H#-So%#k##)#IHSxSpS^SmS]SnSbk##$#k##/#k##2#k##;#k##=#k##?#j##A#%S\s@k%#M5Sb#F%%L2S[&#4#>s@RS>1S[&#'#0S[&#'#$C#s@L$C'#$Cs@b#$C,#$C.#$Cs@e#)ESb3#(D3J(D4K3$#*F2+3s@D#$#*F2+3s@G#$#/SbS\G#$##(##,##0##s###%SisA3%#N6HS]Sn#s$vS[%SbsA6%#M5S]#F%%L2Sk&#4#>s@yS?1Sk&#'#0Sk&#'#$C#s@s$C'#$CsA-#$C,#$C.#$CsA0#)ES]3#(D3J(D4K3$#*F2+3s@k#$#*F2+3s@n#$#/S]SbG#$##(##,##0##s###%SnsAZ%#M5Sm#F%%L2S\&#4#>sAASX1S\&#'#0S\&#'#$C#sA;$C'#$CsAQ#$C,#$C.#$CsAT#)ESm3#(D3J(D4K3$#*F2+3sA3#$#*F2+3sA6#$#/SmSnG#$##(##,##0##s###JSlS^SmKESpS^-SoS^G,S](Q#R:#,Sm;#<$-Ss$#k##'#=Sl-Ss#s@~,S^(Q#R:#,Sp;#=#<%H#-Sq%#k##)#IHT)StSoSxSlSpS^k##$#k##/#k##2#k##;#k##=#k##?#j##A#%S]sBA%#L2Si&#4#>sB&SB1Si&#'#0Si&#'#$C#sA|$C'#$CsB6#$C,#$C.#$CsB9#)ES^3#(D3J(D4K3$#*F2+3sAt#$#*F2+3sAw#$#/S^S]G#$##(##,##0#%SmsBb%#M5Sp#F%S^sBe%#L2Sn&#4#>sBJSC1Sn&#'#0Sn&#'#$C#sBD$C'#$CsBZ#$C,#$C.#$CsB]#)ESl3#(D3J(D4K3$#*F2+3sB<#$#*F2+3sB?#$#/SlS^G#$##(##,##0#%SpsC*%#L2S]&#4#>sBkSa1S]&#'#0S]&#'#$C#sBe$C'#$CsB{#$C,#$C.#$CsB~#)ESx3#(D3J(D4K3$#*F2+3sB]#$#*F2+3sB`#$#/SxSpG#$##(##,##0#JSsSoSxKEStSo-SqSoG,Sl(Q#R:#,Sx;#<$-Su$#k##'#=Ss-Su#sBK,So(Q#R:#,St;#=#<%H#-Sr%#k##)#IHT-SySqT)SsStSok##$#k##/#k##2#k##;#k##=#k##?#j##A#2Sm(D#J(D$K3$#1Sm*F#+$sC0#$#0Sm*F#+$sC4#$#/SoSlG#$##)##.#%SxsCz%#L2S^&#4#>sC_SJ1S^&#'#0S^&#'#$C#sCY$C'#$CsCo#$C,#$C.#$CsCr#)ESt3#2Sp(D#J(D$K3$#1Sp*F#+$sCS#$#0Sp*F#+$sCW#$#/SsSoG#$##)##.#2Sl(D#J(D$K3$#1Sl*F#+$sCc#$#0Sl*F#+$sCg#$#/T)StG#$##)##.#JSuSqT)KESySq-SrSqG,Ss(Q#R:#,T);#<$-Sz$#k##'#=Su-Sz#sCQ,Sq(Q#R:#,Sy;#=#<%H#-Sv%#k##)#IHT*T$SrT-SuSySqk##$#k##/#k##2#k##;#k##=#k##?#j##A#1Sx*F#+$sD2#$#0Sx*F#+$sD6#$#/SqSsG#$##)#2So(D#J(D$K3$#1St*F#+$sDA#$#0St*F#+$sDE#$#/SuSqG#$##)#1Ss*F#+$sDL#$#0Ss*F#+$sDP#$#/T-SyG#$##)#JSzSrT-KET$Sr-SvSrG,Su(Q#R:#,T-;#<$-S{$#k##'#=Sz-S{#sD9,Sr(Q#R:#,T$;#=#<%H#-T+%#k##)#IHT'T,SvT*SzT$Srk##$#k##/#k##2#k##;#k##=#k##?#j##A#0T)*F#+$sDv#$#/SrSuG#$#1Sq*F#+$sD|#$#0Sy*F#+$sE$#$#/SzSrG#$#0Su*F#+$sE*#$#/T*T$G#$#JS{SvT*KET,Sv-T+SvG,Sz(Q#R:#,T*;#<$-S|$#k##'#=S{-S|#sDn,Sv(Q#R:#,T,;#=#<%H#-Sc%#k##)#IHSjS}T+T'S{T,Svk##$#k##/#k##2#k##;#k##=#k##?#j##A#/SvSzG0Sr*F#+$sEP#$#/S{SvGJS}T'S{KET+T'-SjT'G(Q:R:#,S{;#<$-O$#k##'#=S}-O#sE6,T'(Q#R:#,T+;#=#<%H#-S<%#k##)#]TKS<OScSjGSISgT%S$/ScSjG2S}(D#J(D$K3$#1S}*F#+$sEq#$#0S}*F#+$sEu#$#/OScG#$##)#L&%SKIL+%S'#L0%S(##1&9S4DT&S39sFoD#GGsFo#T=FHS3G@S#E#S`)ESwS3#C%A&(D#S-%S3sFl%#S)?#SPS$)ESw$#%&S%%S<S&&#'#&S<'#$C#sFk$C&#)ESw*#%/P8S#7Sw$#%2N,S#6HT=Sw$#O%5M5Sw#F%7L2S#&#4#1S#&#'#0S#&#'#$C#sF^$C'#$CsFt#$CsFm#$C-#$CsFw#)ESw2#(D2J(D3K3$#*F2+3sFV#$#*F2+3sFY#$#/SwS3G#$##(##,##0##B##s#%##s#)##s#-##s#7##s#<##s#?##s#A##s#E##s#G#j#$sG\#DsG]#j#%sG^#DsG_#j#&sG`#DsGa#j#'S4#9S4DT+SP9sGbD#GGsGb#T>FHSPG@OE#S`)ES3SP#C%A&(D#S-%SPsG_%#S)?#S<S$)ES3$#%&S%%S#S&&#'#&S#'#$C#sG^$C&#)ES3*#%/P8O7S3$#%2N,O6HT>S3$#Sc%5M5S3#F%7L2O&#4#1O&#'#0O&#'#$C#sGQ$C'#$CsGg#$CsG`#$C-#$CsGj#)ES32#(D2J(D3K3$#*F2+3sGI#$#*F2+3sGL#$#/S3SPG#$##(##,##0##B##s#%##s#)##s#-##s#7##s#<##s#?##s#A##s#E##s#G#j#$sHO#DsHP#j#%sHQ#DsHR#j#&sHS#9S4DT'S<9sHSD#GGsHS#SwFHS<G@ScE#T*)ESPS<#C%A&(D#S-%S<sHP%#S)?#S#S$)ESP$#%&S%%OS&&#'#&O'#$C#sHO$C&#)ESP*#%/P8Sc7SP$#%2N,Sc6HSwSP$#Sj%5M5SP#F%7L2Sc&#4#1Sc&#'#0Sc&#'#$C#sHB$C'#$CsHX#$CsHQ#$C-#$CsH[#)ESP2#(D2J(D3K3$#*F2+3sH:#$#*F2+3sH=#$#/SPS<G#$##(##,##0##B##s#%##s#)##s#-##s#7##s#<##s#?##s#A##s#E##s#G#j#$sI@#DsIA#j#%sIB#9S4DS{S#9sIBD#GGsIB#S3FHS#G@SjE#Sz)ES<S##C%A&(D#S-%S#sI?%#S)?#OSu)ES<$#%&S%%ScS&&#'#&Sc'#$C#sI>$C&#)ES<*#%/P8Sj7S<$#%2N,Sj6HS3S<$#S|%5M5S<#F%7L2Sj&#4#1Sj&#'#0Sj&#'#$C#sI1$C'#$CsIG#$CsI@#$C-#$CsIJ#)ES<2#(D2J(D3K3$#*F2+3sI)#$#*F2+3sI,#$#/S<S#G#$##(##,##0##B##s#%##s#)##s#-##s#7##s#<##s#?##s#A##s#E##s#G#j#$sJ/#9S4DT,OTsJ<T#T#B#B#B#Q#9sJ6D*#GsJ6#SPFHO%@S|A#&#'#UTL&&#4#UTM)&#4#UTN,UTO#UT9sJJ$sJK$#>sIz#.sIx.#.#>#T$$C#sJ5$C(#$CsJ)#$C/#$C3#$C7#)ES#O#C<(D<S-%OsJI%#F./.#.#.#.#.#.#.#.#>#Sy&TP'#&/'#&TQ'#&TR'#$C#sJR$C&#$C)#$C,#$C/#$Cs#x#)ES#;#BsJ)B#B#Q#%A#%SjS&&#'#&Sj'#$C#sJc$C&#)ES#*#Bs#PB#B#Q#%s#.#8S|7S#$#B4Q#%s#3#,S|6HSPS#$#S}TsK;B#B#B#B#B#Q#%s#=#5S##FBsJLT#B#B#B#B#Q#%s#F#2S|&#4#>sJqSt1S|&#'#0S|&#'#$C#sJk$C'#$CsK%#$C,#$C.#$CsK(#)ES#3#(D3J(D4K3$#*F2+3sJc#$#*F2+3sJf#$#/S#Os$%#$##(##,##0##s#*##s#4##s#:##s#B##s#P##s#l##s#n##s#p##s$/#UT0s#sUSU#UT9T?UT/T?VTSDS$UTTDUTUDVTVDT8MD#Sd#N%SeS7S7S_#SfVTW&S_RT@TAVTXIS`(T@#TAm$%#WTYDFS$XTZIS`$#l#(*)#l#)0/#l#*32#j#+D#*IIk#+D#UIS#l#,&$#*OOm#$#.s$$.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#USU#%O#%Os$`*$#*s$B$j#-DI*S$IUT[#j#.D#j#-D#%S$IXT\DDT]#RD#j#/D#j#0D#RDOUSUIRD#j#-T.#RDsL<`T1T.DDDSUSU11$7sL=#fT2DDDDDDS~222S~)OO(7sL>#RD6`T3DDT#4T#08s$U$77#SDsLAODs#?#SDs$xODs#A#MD%Sd#Ns#DSeS7S7S_#Sfl#(#s#As#;l#)s#Hs#G#l#*s#Ks#J#j#+D#%IsLK%Is%%*$#k#+D#l#,'#s#<XT4s#&s#%2#%Os#T*#s#)m#%#\T(S3Os%-Os#WSgs#>#^T5ES3S<S#Os$nSkSHSI#UT0s$RUSU#SDFOD9#MDs#WSd#Ns#YSeS7S7S_#Sfl#(#s#Vs#Pl#)s#]s#\#l#*s#`s#_#j#+D#%7F*I#k#+D#l#,&#s#P*Os$xm#$#.s#@.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#USU#%s%7#*#s#W%s%9s$x*#s#YRDs%;RDs${`T1T.DDDSUSUs#Ys#Ys#L*s$|#fT2DDDDDDS~s#Zs#Zs#ZS~s#Qs%>s%>%*s$}#`T3DDT#s#[T#s#W*(#s#^s#^s#JSDs%#ODs#2#MD#Sds#HNs$-SeS7S7S_#Sfl#(#s$*s$$l#)s$1s$0#l#*s$4s$3#j#+D#%s#2s%+*#s#Gk#+D#l#,&#s$$XT464/#%s%Ms#@*#s#mm#%#\T(S3Os%qs%Ps#CSgs#5#^T5ES3S<S#s%Qs%9SaSHSI#UT0s%-USU#ODs#\6MDs$>Sd#Ns$@SeS7S7S_#Sfl#(#s$=s$7l#)s$Ds$C#l#*s$Gs$F#j#+D#%s#Zs%>*I#k#+D#l#,&#s$7*Os%Am#$#USUs%X%s%D#*#s$&QsMg%s%G#*#s$)RDs%IRD&`T1T.DDDSUSUs$)s$)s#xs%`'#fT2DDDDDDS~s$*s$*s$*S~s#}s%Ls%L%+(#`T3DDT#s$+T#s$'+(#s$.s$.s#vSD*OD;#MD#Sds#tNs$YSeS7S7S_#Sfl#(#s$Vs$Pl#)s$]s$\#l#*s$`s$_#j#+D#%;2*#s#sk#+D#l#,&#s$PXT474/#%s%[s#(*#s$=m#%#\T(S3Os&As%^s#+Sg>#^T5ES3S<S#s%_s%XSXSHSI#SDs%TODs$+#MDs$iSd#Ns$kSeS7S7S_#Sfl#(#s$hs$bl#)s$os$n#l#*s$rs$q#j#+D#%s$)s%\*I#k#+D#l#,&#s$bQs%TSD#OD/#MD#Sds$7Ns$xSeS7S7S_#Sfl#(#s$us$ol#)s$|s${#l#*s%#s$~#j#+D#%/+*#s$6k#+D#l#,&#s$o%s%lTB*#s$[m#%#\T(S3Os&_s%oTBSg3#]T^S3S<S#s%ps%oSTSHSI#SDs%mODs$I#MDs%+Sd#Ns%-SeS7S7S_#Sfl#(#s%*s%$l#)s%1s%0#l#*s%4s%3#j#+D#%s$Gs%u*I#k#+D#l#,&#s%$Bs%lB#B#Q#SD#OD2#MD#Sds$XNs%=SeS7S7S_#Sfl#(#s%:s%4l#)s%As%@#l#*s%Ds%C#j#+D#%2+*#s$Wk#+D#l#,&#s%4%s&,TC*#s$|m#%#\T(S3Os'$s&/TCSg6#aT_S3SPS<S#s&0s&/S}SSSHSI#T%S`SDs&(ODs$j#MDs%LSd#Ns%NSeS7S7S_#Sfl#(#s%Ks%El#)s%Rs%Q#l#*s%Us%T#j#+D#%s$hs&0*I#k#+D#l#,&#s%EOD-?MD#Sds$tNs%YSeS7S7S_#Sfl#(#s%Vs%Pl#)s%]s%\#l#*s%`s%_#j#+D#%-s#'*#s$sk#+D#l#,&#s%P%s&>TD*#s%<m#%#\T(S3Os'@s&ATDSg1#]T`S3S<S#s&BFSLSHSI#UT0s&*USU#SDs&=ODs%,#MDs%jSd#Ns%lSeS7S7S_#Sfl#(#s%is%cl#)s%ps%o#l#*s%ss%r#j#+D#%s%*s&E*I#k#+D#l#,&#s%c*Os&Hm#$#.s$Z.#.#.#.#.#.#.#.#.#.#.#.#.#.#.#USU#%s&[#*#s%b%s&]s&v*#s%dRDs&_RDs&y`T1T.DDDSUSUs%ds%ds%W*s&z#fT2DDDDDDS~s%es%es%eS~s%\s&bs&b%*s&{#`T3DDT#s%fT#s%b*(#s%is%is%UODs#)s$+MD#Sds%RNs&7SeS7S7S_#Sfl#(#s&4s&.l#)s&;s&:#l#*s&>s&=#j#+D#%s#)s'(*#s%Qk#+D#l#,&#s&.XT453.#%s&ps#7*#s%wm#%#\T(S3Os'{s&ss#:Sgs#,#^T5ES3S<S#s&ts&dS2SHSI#Ls&ds&W#ILs&~s&Ws#?#Ls',s&Ws#\#Ls'2s&Ws#~#Ls':s&Ws$A#Ls'Hs&Ws$n#Ls'ds&WSV#Ls'fs&WSh#Ls'hs&Ws%Y#Ls('s&WSn#Ls()s&WSp#9sO_Ds(3GGsO_#SPFHOGEs(+T$)ES#O#%s'mS)?#ScSy)ES#$#%s'pS%)ES##s'K%s'rP7S##s'F%s'tN6HSPS##s'CS}%s'vM5S##F%s'xL)ES##s'%/S#OG#s&y##s&}##s'%##'##*##-##0##3##6##s()##s(+##<##?##A#m#s#$#XT6sP's(VSt#XT6sP(s)DSy#XT6sP)s*4T$#XT6S4s+&T,#l#1s+ws+v#l#2s,/s,.#j#3s,1#j#4s,<#j#5s,?#j#6s,G#j#7s,I#j#8s,K#j#9s,M#j#:s,O#V#S$Ij##s,U#j##s,x#Ps,ys,xs,X#Ij#;s,~#j#<s-)#V#S$Ij##s-/#j##s-\#Ps-]s-Ws-7#Ij#;s-b#j#=s-n#V#S$Ij##s-t#j##s.O#Ps.Ps.Es.%#Ij#;s.U#j#>s.f#V#S$Ij##s.{#j##s/]#Ps/^s/Qs/1#Ij#;s/r#j#?s08#V#S$Ij##s0=#j##s1C#Ps1Ds1$s0`#Ij#;s1H#j#@s1m#V#S$Ij##s1r#j##s2~#Ps3#s2\s2<#Ij#;s3'#j#As3O#V#S$Ij##s3U#j##s4g#Ps4hs4Bs3~#Ij#;s4m#j#Bs5=#V#S$Ij##s5I#j##s6c#Ps6ds6:s5v#Ij#;s6o#j#Cs7I#V#S$Ij##s7O#j##s8}#Ps8~s8Js8*#Ij#;s9'#j#Ds9a#V#S$Ij##s9f#j##s;A#Ps;Bs:es:E#Ij#;s;F#j#Es<(#V#S$Ij##s<,#j##s=j#Ps=ks=/s<k#Ij#;s=n#j#Fs>R#V#S$Ij##s>W#j##s@=#Ps@>s?\s?<#Ij#;s@B#j#GsA)#V#S$Ij##sA,#j##sBu#PsBvsB4sAp#Ij#;sBx#j#HsCa#V#S$Ij##sCf#j##sEW#PsEXsDpsDP#Ij#;sE\#j#$sQ,#V#S$Ij##sFJ#j#-sQ/#YT7sQ0sGYsG9#Ij#;sHF#j#%sQ2#V#S$Ij##sI6#j#-sQ5#YT7sQ6sJGsJ'#Ij#;sK6#j#&sQ8#V#S$Ij##sL(#j#-sQ;#YT7sQ<sM;sLw#Ij#;sN,#j#'S4#V#S$Ij##sN|#j#-S4#YT7S4sP5sOq#Ij#;sQB#j#IsQD#j#JTa#j#KD#j#LD#j#MD#j#NsQJ#j#/Tb#j#OsQX#j#PsQZ##"). Qed.

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
  ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Numbers.BinNums.Z); constr:(@stdpp.bitvector.definitions.bv_wrap); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@stdpp.bitvector.definitions.bv_extract); constr:(@Corelib.Numbers.BinNums.N0); constr:(@LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.le4); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.list); constr:(@LinuxProcessSemantics.LinuxProcessSem.BvBase.Z_to_le_bytes); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.of_N); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep2.KIT.Z_to_le_bytes_4_congr); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Stdlib.ZArith.Zdiv.Zplus_mod_idemp_l); constr:(@Stdlib.ZArith.BinInt.Z.mod_mod); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.le_bytes_to_word_le4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.extract_low_mod); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.NArith.BinNat.N.lt); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Numbers.BinNums.N); constr:(@Stdlib.ZArith.Znat.N2Z.inj_lt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@stdpp.bitvector.definitions.bv_add); constr:(@stdpp.bitvector.definitions.bv_add_unsigned); constr:(@LinuxProcessSemantics.Riscv.Sem.amo_val); constr:(@LinuxProcessSemantics.Riscv.Instr.AMO_ADD)|] [|@z; @Ha; @__ff; @__varmap; @__wit; @__arith; @__sat1; @__sat0; @s; @v|] "#$j#&#j#.###E#$#R#S#3#%#Q#7#=#<#>#G#L#U#T#Y#\#]#d#D#,#5#4#2#:#A#C#H#J#I#K#M#N#P#V#X#O#Z#^#_#[#`#?#a#e#f#g#h#c#b#i#j#k#l#;#6#0#1#-#+#8#@#/#9#*#)#F#W#B3#[%#\&#]%#^%#_)#`$#a%#b%#c%#d$#e$#f$#8%#g%#h%#i&(S)(#(#(#(#(#-#.#-&.#US*FUS+#XS,(I&#&'#&(D%$#+*#-1.#UL#,S-,#,#,#)#D&5J&4F%$#UM>UM;VN$##&#)+#$0+#j#$C#&?:UO>VN+##%#%D/+B#)4#$9#,j#$C#&s#(F##1#D+%#7+s#*#)<#$A#4j#$C##)1%#s#)+s#0#%-s#+##<#.=%#s#.##?#?@$CD#j#$C##:s##$C#&j#$C##s#+s#&%#s#+##s#($C#Dj#$C#$CDs#*j#$C#*C3%?s#>##s#/WS.Bs#@s#0'C7'&$##8s#2VS/s#5s#4/Es#60Es#6/Es#6k##$#k##&#0Es#;WS0s#<s#;Fj##P#j#%%#0Es#=k##P#k#%(#VS1Es#B*S2#m##0UF#US3QULQUS4CUS5CUS6C1Cs#KWS7C#s#`1CEXRC$S8#[S#'KGGH#S$ZS9(KGGH#VS:)H*S%S&VS;DJ$S%#S&m$%#WS<CEFXS=DJ$#l#&*)#l#'32#l#(65#$Cs#YEk###S>l#)%#Dl#*;s#'#l#+s##@#l#*s#-s#(#2s#Fs#_#'Cs#Fs#8s#1s#0#2s#Ss#a%'Cs#Ss#?$s#G##s#Fs#c2s#Hs#d('Cs#Hs#E%$##s#Ns#f$C#s#7m#%#WS?s#Qs#O#US@F'Cs#\s#V$s#f#VS'Is$&/Es#n*CE*Cs#p`SASBCS'OS(SCIE$s$*s#q#1Cs#rXRCs#)SD#[S#s#-KGGH#S$l#&#s#'Al#'s#1s#0#l#(s#4s#3#l#)#,DXSE.-*#WSFs$3s$0#'Cs#rs#m1s$/#WSGs$5s$1D&s$6#WSHs$7s$3D'Cs$0s#z&$#XSIs$9SJs$5D&s$:#)s$,#)s$-s#h$s$2$#m#(#j#,s$>#j#-s$A##"). Qed.

(* [comment removed for export] *)
Lemma amo_old32 : forall v : word, sext 64 (bv_extract 0 32 (le_bytes_to_word (le4 v))) = sx32 v.
Proof. exact sext_extract_le4. Qed.

End KIT.

