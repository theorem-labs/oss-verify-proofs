(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXRep AXRep2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HE_END_OF_STREAM := 1.   Definition HE_PARTIAL_MESSAGE := 2.   
Definition HE_BUFFER_OVERFLOW := 7. Definition HE_HEADER_LIMIT := 8.      Definition HE_BODY_LIMIT := 9.
Definition HE_BAD_METHOD := 12.     Definition HE_BAD_TARGET := 13.
Definition HE_BAD_VERSION := 14.   Definition HE_BAD_FIELD := 17.        Definition HE_BAD_VALUE := 18.
Definition HE_BAD_CONTENT_LENGTH := 19. Definition HE_BAD_TRANSFER_ENCODING := 20. Definition HE_BAD_CHUNK := 21.
Definition HE_BAD_CHUNK_EXTENSION := 22. Definition HE_MULTIPLE_CONTENT_LENGTH := 24.
Definition HE_FIELD_NAME_TOO_LARGE := 27. Definition HE_FIELD_VALUE_TOO_LARGE := 28.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALOC_TCNE_NAME     : Z := 0x1166c8.   (* [comment removed for export] *)
Definition ALOC_TCNE_VALUE    : Z := 0x1166e0.   (* [comment removed for export] *)
Definition ALOC_RDPUT_OVF     : Z := 0x117120.   (* [comment removed for export] *)
Definition ALOC_RS_OVF        : Z := 0x117788.   (* [comment removed for export] *)
Definition ALOC_RS_EOS        : Z := 0x1177a0.   (* [comment removed for export] *)
Definition ALOC_PUT_NM        : Z := 0x1177b8.   (* [comment removed for export] *)
Definition ALOC_PSL_HL        : Z := 0x1177d0.   (* [comment removed for export] *)
Definition ALOC_ISL_BADVER    : Z := 0x1177e8.   (* [comment removed for export] *)
Definition ALOC_ISL_NM        : Z := 0x117800.   (* [comment removed for export] *)
Definition ALOC_ISL_BADVER2   : Z := 0x117818.   (* [comment removed for export] *)
Definition ALOC_PM_NM         : Z := 0x117830.   (* [comment removed for export] *)
Definition ALOC_PM_BAD        : Z := 0x117848.   (* [comment removed for export] *)
Definition ALOC_PM_EMPTY      : Z := 0x117860.   (* [comment removed for export] *)
Definition ALOC_PT_NM         : Z := 0x117878.   (* [comment removed for export] *)
Definition ALOC_PT_BAD        : Z := 0x117890.   (* [comment removed for export] *)
Definition ALOC_PT_EMPTY      : Z := 0x1178a8.   (* [comment removed for export] *)
Definition ALOC_PV_NM         : Z := 0x1178c0.   (* [comment removed for export] *)
Definition ALOC_PV_H          : Z := 0x1178d8.   (* [comment removed for export] *)
Definition ALOC_PV_T1         : Z := 0x1178f0.   (* [comment removed for export] *)
Definition ALOC_PV_T2         : Z := 0x117908.   (* [comment removed for export] *)
Definition ALOC_PV_P          : Z := 0x117920.   (* [comment removed for export] *)
Definition ALOC_PV_SLASH      : Z := 0x117938.   (* [comment removed for export] *)
Definition ALOC_PV_D1         : Z := 0x117950.   (* [comment removed for export] *)
Definition ALOC_PV_DOT        : Z := 0x117968.   (* [comment removed for export] *)
Definition ALOC_PV_D2         : Z := 0x117980.   (* [comment removed for export] *)
Definition ALOC_PF_HL         : Z := 0x117998.   (* [comment removed for export] *)
Definition ALOC_IPF_NM        : Z := 0x1179b0.   (* [comment removed for export] *)
Definition ALOC_IPF_BADLE     : Z := 0x1179c8.   (* [comment removed for export] *)
Definition ALOC_PFD_0         : Z := 0x1179e0.   (* [comment removed for export] *)
Definition ALOC_PFD_1         : Z := 0x1179f8.   (* [comment removed for export] *)
Definition ALOC_PFD_2         : Z := 0x117a10.   (* [comment removed for export] *)
Definition ALOC_PFD_3         : Z := 0x117a28.   (* [comment removed for export] *)
Definition ALOC_PFD_4         : Z := 0x117a40.   (* [comment removed for export] *)
Definition ALOC_PFD_5         : Z := 0x117a58.   (* [comment removed for export] *)
Definition ALOC_PFD_6         : Z := 0x117a70.   (* [comment removed for export] *)
Definition ALOC_PFD_7         : Z := 0x117a88.   (* [comment removed for export] *)
Definition ALOC_PFD_8         : Z := 0x117aa0.   (* [comment removed for export] *)
Definition ALOC_PFD_9         : Z := 0x117ab8.   (* [comment removed for export] *)
Definition ALOC_PFD_10        : Z := 0x117ad0.   (* [comment removed for export] *)
Definition ALOC_PFD_11        : Z := 0x117ae8.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALOC_DF_TE1        : Z := 0x117b48.   (* [comment removed for export] *)
Definition ALOC_DF_TE2        : Z := 0x117b60.   (* [comment removed for export] *)
Definition ALOC_DF_BADVAL     : Z := 0x117b78.   (* [comment removed for export] *)
Definition ALOC_DF_BADCL      : Z := 0x117b90.   (* [comment removed for export] *)
Definition ALOC_DF_MULTICL    : Z := 0x117ba8.   (* [comment removed for export] *)
Definition ALOC_FH_TE1        : Z := 0x117bc0.   (* [comment removed for export] *)
Definition ALOC_FH_TE2        : Z := 0x117bd8.   (* [comment removed for export] *)
Definition ALOC_FH_BODYLIM    : Z := 0x117bf0.   (* [comment removed for export] *)
Definition ALOC_PBE_BODYLIM   : Z := 0x117c08.   (* [comment removed for export] *)
Definition ALOC_PCH_NM        : Z := 0x117c20.   (* [comment removed for export] *)
Definition ALOC_PCH_BADCRLF   : Z := 0x117c38.   (* [comment removed for export] *)
Definition ALOC_PCH_NM2       : Z := 0x117c50.   (* [comment removed for export] *)
Definition ALOC_PCH_BADHEX    : Z := 0x117c68.   (* [comment removed for export] *)
Definition ALOC_PCH_EXT8K     : Z := 0x117c80.   (* [comment removed for export] *)
Definition ALOC_PCH_BODYLIM   : Z := 0x117c98.   (* [comment removed for export] *)
Definition ALOC_PCH_EXTJUNK   : Z := 0x117cb0.   (* [comment removed for export] *)
Definition ALOC_FEOL_BADLE    : Z := 0x117cc8.   (* [comment removed for export] *)
Definition ALOC_PCE_0         : Z := 0x117ce0.   (* [comment removed for export] *)
Definition ALOC_PCE_1         : Z := 0x117cf8.   (* [comment removed for export] *)
Definition ALOC_PCE_2         : Z := 0x117d10.   (* [comment removed for export] *)
Definition ALOC_PCE_3         : Z := 0x117d28.   (* [comment removed for export] *)
Definition ALOC_DBP_FB        : Z := 0x117d40.   (* [comment removed for export] *)
Definition ALOC_TS_EOF        : Z := 0x117d58.   (* [comment removed for export] *)
Definition ALOC_PEOF_1        : Z := 0x117d70.   (* [comment removed for export] *)
Definition ALOC_PEOF_2        : Z := 0x117d88.   (* [comment removed for export] *)
Definition ALOC_PCH_EXT8K'    : Z := 0x117c50.   (* [comment removed for export] *)
Definition ALOC_PCH_NM2'      : Z := 0x117c68.   (* [comment removed for export] *)
Definition ALOC_PCH_BADHEX'   : Z := 0x117c80.   (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TAB_IS_TOKEN_CHAR : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%Z.
(* [comment removed for export] *)
Definition TAB_IS_PATHCHAR : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%Z.
(* [comment removed for export] *)
Definition TAB_IS_TOKEN_LIT : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%Z.
(* [comment removed for export] *)
Definition TAB_UNHEX : list Z := [-1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; -1; -1; -1; -1; -1; -1; -1; 10; 11; 12; 13; 14; 15; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; 10; 11; 12; 13; 14; 15; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1]%Z.
(* [comment removed for export] *)
Definition TAB_IS_QPCHAR : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%Z.
(* [comment removed for export] *)
Definition TAB_IS_QDCHAR : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%Z.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AL_TAB_IS_TOKEN_CHAR   : Z := 0x28b80.   (* [comment removed for export] *)
Definition AL_TAB_IS_PATHCHAR     : Z := 0x29c00.   (* [comment removed for export] *)
Definition AL_TAB_IS_TOKEN_LIT    : Z := 0x29d80.   (* [comment removed for export] *)
Definition AL_TAB_UNHEX           : Z := 0x2a140.   (* [comment removed for export] *)
Definition AL_TAB_IS_QPCHAR       : Z := 0x2a280.   (* [comment removed for export] *)
Definition AL_TAB_IS_QDCHAR       : Z := 0x2a380.   (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_tchar (c : Z) : bool := negb (nth (Z.to_nat c) TAB_IS_TOKEN_CHAR 0 =? 0).
Definition is_pathchar (c : Z) : bool := negb (nth (Z.to_nat c) TAB_IS_PATHCHAR 0 =? 0).
Definition unhex (c : Z) : Z := nth (Z.to_nat c) TAB_UNHEX (-1).
Definition is_qpchar (c : Z) : bool := negb (nth (Z.to_nat c) TAB_IS_QPCHAR 0 =? 0).
Definition is_qdchar (c : Z) : bool := negb (nth (Z.to_nat c) TAB_IS_QDCHAR 0 =? 0).
Definition is_digitc (c : Z) : bool := (48 <=? c) && (c <=? 57).
Definition is_ws (c : Z) : bool := (c =? 32) || (c =? 9).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lowerc (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Record pcore := mkPC {
  pc_blim_has : Z ; pc_blim : Z ; pc_len : Z ; pc_len0 : Z ; pc_skip : Z ;
  pc_hlim : Z ; pc_state : Z ; pc_f : Z }.

Definition ParserCoreCells (c : pcore) (pad7 pad2 : list byte) : list cell :=
  [C8 (wz AVP_PARSER); C1 (b8 (pc_blim_has c)); CB 7 pad7; C8 (wz (pc_blim c));
   C8 (wz (pc_len c)); C8 (wz (pc_len0 c)); C8 (wz 0); C8 (wz 0); C8 (wz (pc_skip c));
   C4 (wz (pc_hlim c)); C2 (wz 0); CB 2 pad2; C4 (wz (pc_state c)); C4 (wz (pc_f c))].

Definition pcore_ok (c : pcore) : Prop :=
  (pc_blim_has c = 0 \/ pc_blim_has c = 1) /\ 0 <= pc_blim c <= 2^20 /\ 0 <= pc_len c < 2^64 /\ 0 <= pc_len0 c < 2^64
  /\ 0 <= pc_skip c < 2^64 /\ 0 <= pc_hlim c <= 8194 /\ In (pc_state c) [0;1;2;3;4;7;8;9;10;11] /\ 0 <= pc_f c < 2^14.

Definition AParserCore (m : mem) (P : Z) (c : pcore) : Prop :=
  exists pad7 pad2, rw_cells asegs m P (ParserCoreCells c pad7 pad2) /\ pcore_ok c.

(* [comment removed for export] *)
Definition FL_EAGER := 2. Definition FL_HASBODY := 8. Definition FL_HTTP11 := 16. Definition FL_EXPECT_CRLF := 64.
Definition FL_CONN_CLOSE := 128. Definition FL_CONN_UPGRADE := 256. Definition FL_CONN_KEEPALIVE := 512.
Definition FL_CONTENT_LENGTH := 1024. Definition FL_CHUNKED := 2048. Definition FL_UPGRADE := 4096. Definition FL_TE := 8192.

(* [comment removed for export] *)
Definition ACharBuf (m : mem) (a : Z) (bs : list byte) (junk : list byte) : Prop :=
  rw_cells asegs m a [C8 (wz (Z.of_nat (length bs))); CB (length bs) bs; CB (4096 - length bs) junk]
  /\ (length bs <= 4096)%nat.

(* [comment removed for export] *)
Definition TokItCells (vp vl it first last : Z) : list cell :=
  [C8 (wz vp); C8 (wz vl); C8 (wz it); C8 (wz first); C8 (wz last)].
Definition OptItCells (lst it vp vl err : Z) (pad7 : list byte) : list cell :=
  [C8 (wz lst); C8 (wz it); C8 (wz vp); C8 (wz vl); C1 (b8 err); CB 7 pad7].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FieldsHdrCells (root lmost rmost : Z) (color : Z) (lnext lprev : Z) (mp ml tp tl ver vb : Z) (pad4 : list byte)
  : list cell :=
  [C8 (wz root); C8 (wz lmost); C8 (wz rmost); C4 (wz color); CB 4 pad4;
   C8 (wz lnext); C8 (wz lprev); C8 (wz mp); C8 (wz ml); C8 (wz tp); C8 (wz tl); C4 (wz ver); C4 (wz vb)].

(* [comment removed for export] *)
Definition MBufHdrCells (lnext lprev out insz inpos outpos outend : Z) : list cell :=
  [C8 (wz 0x1fffffffffffffff); C8 (wz lnext); C8 (wz lprev); C8 (wz out); C8 (wz insz); C8 (wz inpos);
   C8 (wz outpos); C8 (wz outend)].

End HCW.
