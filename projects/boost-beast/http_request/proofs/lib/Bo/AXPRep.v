(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXRep AXRep2.
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
Definition ALOC_TCNE_NAME     : Z := 0x11aa08.   (* [comment removed for export] *)
Definition ALOC_TCNE_VALUE    : Z := 0x11aa20.   (* [comment removed for export] *)
Definition ALOC_RDPUT_OVF     : Z := 0x11b460.   (* [comment removed for export] *)
Definition ALOC_RS_OVF        : Z := 0x11bac8.   (* [comment removed for export] *)
Definition ALOC_RS_EOS        : Z := 0x11bae0.   (* [comment removed for export] *)
Definition ALOC_PUT_NM        : Z := 0x11baf8.   (* [comment removed for export] *)
Definition ALOC_PSL_HL        : Z := 0x11bb10.   (* [comment removed for export] *)
Definition ALOC_ISL_BADVER    : Z := 0x11bb28.   (* [comment removed for export] *)
Definition ALOC_ISL_NM        : Z := 0x11bb40.   (* [comment removed for export] *)
Definition ALOC_ISL_BADVER2   : Z := 0x11bb58.   (* [comment removed for export] *)
Definition ALOC_PM_NM         : Z := 0x11bb70.   (* [comment removed for export] *)
Definition ALOC_PM_BAD        : Z := 0x11bb88.   (* [comment removed for export] *)
Definition ALOC_PM_EMPTY      : Z := 0x11bba0.   (* [comment removed for export] *)
Definition ALOC_PT_NM         : Z := 0x11bbb8.   (* [comment removed for export] *)
Definition ALOC_PT_BAD        : Z := 0x11bbd0.   (* [comment removed for export] *)
Definition ALOC_PT_EMPTY      : Z := 0x11bbe8.   (* [comment removed for export] *)
Definition ALOC_PV_NM         : Z := 0x11bc00.   (* [comment removed for export] *)
Definition ALOC_PV_H          : Z := 0x11bc18.   (* [comment removed for export] *)
Definition ALOC_PV_T1         : Z := 0x11bc30.   (* [comment removed for export] *)
Definition ALOC_PV_T2         : Z := 0x11bc48.   (* [comment removed for export] *)
Definition ALOC_PV_P          : Z := 0x11bc60.   (* [comment removed for export] *)
Definition ALOC_PV_SLASH      : Z := 0x11bc78.   (* [comment removed for export] *)
Definition ALOC_PV_D1         : Z := 0x11bc90.   (* [comment removed for export] *)
Definition ALOC_PV_DOT        : Z := 0x11bca8.   (* [comment removed for export] *)
Definition ALOC_PV_D2         : Z := 0x11bcc0.   (* [comment removed for export] *)
Definition ALOC_PF_HL         : Z := 0x11bcd8.   (* [comment removed for export] *)
Definition ALOC_IPF_NM        : Z := 0x11bcf0.   (* [comment removed for export] *)
Definition ALOC_IPF_BADLE     : Z := 0x11bd08.   (* [comment removed for export] *)
Definition ALOC_PFD_0         : Z := 0x11bd20.   (* [comment removed for export] *)
Definition ALOC_PFD_1         : Z := 0x11bd38.   (* [comment removed for export] *)
Definition ALOC_PFD_2         : Z := 0x11bd50.   (* [comment removed for export] *)
Definition ALOC_PFD_3         : Z := 0x11bd68.   (* [comment removed for export] *)
Definition ALOC_PFD_4         : Z := 0x11bd80.   (* [comment removed for export] *)
Definition ALOC_PFD_5         : Z := 0x11bd98.   (* [comment removed for export] *)
Definition ALOC_PFD_6         : Z := 0x11bdb0.   (* [comment removed for export] *)
Definition ALOC_PFD_7         : Z := 0x11bdc8.   (* [comment removed for export] *)
Definition ALOC_PFD_8         : Z := 0x11bde0.   (* [comment removed for export] *)
Definition ALOC_PFD_9         : Z := 0x11bdf8.   (* [comment removed for export] *)
Definition ALOC_PFD_10        : Z := 0x11be10.   (* [comment removed for export] *)
Definition ALOC_PFD_11        : Z := 0x11be28.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALOC_DF_TE1        : Z := 0x11be88.   (* [comment removed for export] *)
Definition ALOC_DF_TE2        : Z := 0x11bea0.   (* [comment removed for export] *)
Definition ALOC_DF_BADVAL     : Z := 0x11beb8.   (* [comment removed for export] *)
Definition ALOC_DF_BADCL      : Z := 0x11bed0.   (* [comment removed for export] *)
Definition ALOC_DF_MULTICL    : Z := 0x11bee8.   (* [comment removed for export] *)
Definition ALOC_FH_TE1        : Z := 0x11bf00.   (* [comment removed for export] *)
Definition ALOC_FH_TE2        : Z := 0x11bf18.   (* [comment removed for export] *)
Definition ALOC_FH_BODYLIM    : Z := 0x11bf30.   (* [comment removed for export] *)
Definition ALOC_PBE_BODYLIM   : Z := 0x11bf48.   (* [comment removed for export] *)
Definition ALOC_PCH_NM        : Z := 0x11bf60.   (* [comment removed for export] *)
Definition ALOC_PCH_BADCRLF   : Z := 0x11bf78.   (* [comment removed for export] *)
Definition ALOC_PCH_NM2       : Z := 0x11bf90.   (* [comment removed for export] *)
Definition ALOC_PCH_BADHEX    : Z := 0x11bfa8.   (* [comment removed for export] *)
Definition ALOC_PCH_EXT8K     : Z := 0x11bfc0.   (* [comment removed for export] *)
Definition ALOC_PCH_BODYLIM   : Z := 0x11bfd8.   (* [comment removed for export] *)
Definition ALOC_PCH_EXTJUNK   : Z := 0x11bff0.   (* [comment removed for export] *)
Definition ALOC_FEOL_BADLE    : Z := 0x11c008.   (* [comment removed for export] *)
Definition ALOC_PCE_0         : Z := 0x11c020.   (* [comment removed for export] *)
Definition ALOC_PCE_1         : Z := 0x11c038.   (* [comment removed for export] *)
Definition ALOC_PCE_2         : Z := 0x11c050.   (* [comment removed for export] *)
Definition ALOC_PCE_3         : Z := 0x11c068.   (* [comment removed for export] *)
Definition ALOC_DBP_FB        : Z := 0x11c080.   (* [comment removed for export] *)
Definition ALOC_TS_EOF        : Z := 0x11c098.   (* [comment removed for export] *)
Definition ALOC_PEOF_1        : Z := 0x11c0b0.   (* [comment removed for export] *)
Definition ALOC_PEOF_2        : Z := 0x11c0c8.   (* [comment removed for export] *)
Definition ALOC_PCH_EXT8K'    : Z := 0x11bf90.   (* [comment removed for export] *)
Definition ALOC_PCH_NM2'      : Z := 0x11bfa8.   (* [comment removed for export] *)
Definition ALOC_PCH_BADHEX'   : Z := 0x11bfc0.   (* [comment removed for export] *)

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
Definition AL_TAB_IS_TOKEN_CHAR   : Z := 0x28c80.   (* [comment removed for export] *)
Definition AL_TAB_IS_PATHCHAR     : Z := 0x29d40.   (* [comment removed for export] *)
Definition AL_TAB_IS_TOKEN_LIT    : Z := 0x29ec0.   (* [comment removed for export] *)
Definition AL_TAB_UNHEX           : Z := 0x2a2e0.   (* [comment removed for export] *)
Definition AL_TAB_IS_QPCHAR       : Z := 0x2a420.   (* [comment removed for export] *)
Definition AL_TAB_IS_QDCHAR       : Z := 0x2a520.   (* [comment removed for export] *)
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
  exists pad7 pad2, rw_cells bsegs m P (ParserCoreCells c pad7 pad2) /\ pcore_ok c.

(* [comment removed for export] *)
Definition FL_EAGER := 2. Definition FL_HASBODY := 8. Definition FL_HTTP11 := 16. Definition FL_EXPECT_CRLF := 64.
Definition FL_CONN_CLOSE := 128. Definition FL_CONN_UPGRADE := 256. Definition FL_CONN_KEEPALIVE := 512.
Definition FL_CONTENT_LENGTH := 1024. Definition FL_CHUNKED := 2048. Definition FL_UPGRADE := 4096. Definition FL_TE := 8192.

(* [comment removed for export] *)
Definition ACharBuf (m : mem) (a : Z) (bs : list byte) (junk : list byte) : Prop :=
  rw_cells bsegs m a [C8 (wz (Z.of_nat (length bs))); CB (length bs) bs; CB (4096 - length bs) junk]
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
