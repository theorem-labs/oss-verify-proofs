(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AGOT_SHBASE  : Z := 0x5ae698.  (* [comment removed for export] *)
Definition AGOT_UAR     : Z := 0x5ae6f0.  (* [comment removed for export] *)
Definition AGOT_MEMSETP : Z := 0x5ae6b8.  (* [comment removed for export] *)
Definition AGOT_FLAGS   : Z := 0x5ae690.  (* [comment removed for export] *)
Definition AGOT_CFLAGS  : Z := 0x5ae688.  (* [comment removed for export] *)
Definition AGOT_HIEND   : Z := 0x5ae6b0.  (* [comment removed for export] *)
Definition AGOT_MIDBEG  : Z := 0x5ae6a0.  (* [comment removed for export] *)
Definition AGOT_MIDEND  : Z := 0x5ae6a8.  (* [comment removed for export] *)
Definition AGOT_SEALED  : Z := 0x5ae6d8.  (* [comment removed for export] *)
Definition AGOT_DYING   : Z := 0x5ae6e0.  (* [comment removed for export] *)
Definition AGOT_PGSZ    : Z := 0x5ae678.  (* [comment removed for export] *)
Definition AGOT_RINTRIN : Z := 0x5af220.  (* [comment removed for export] *)
Definition AGOT_FSTLS   : Z := 0x5b0668.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASHBASE_CELL : Z := 0x6772b8.
Definition AUAR_CELL    : Z := 0x6772c0.
Definition AMEMSETP_CELL : Z := 0x5b18d0.   Definition AREAL_MEMSET : Z := 0x530800.
Definition AINITED_CELL : Z := 0x677f98.
Definition ARINTRIN_CELL : Z := 0x677f99.
Definition AHIEND_CELL  : Z := 0x677fa0.
Definition AMIDBEG_CELL : Z := 0x677fa8.
Definition AMIDEND_CELL : Z := 0x677fb0.
Definition ADYING_CELL  : Z := 0x708ddc.
Definition APGSZ_CELL   : Z := 0x706d60.
Definition ACANPOISON_CELL : Z := 0x676b1c.
Definition AMEMCPYP_CELL : Z := 0x5b18c8.   Definition AREAL_MEMCPY : Z := 0x5303cc.   (* [comment removed for export] *)
Definition ASTRLENP_CELL : Z := 0x5b16a8.   Definition AREAL_STRLEN : Z := 0x530cfc.   (* [comment removed for export] *)
Definition ACF_ISTRLEN_CELL : Z := 0x708ee3.  (* [comment removed for export] *)
Definition ACF_STRICT_CELL  : Z := 0x708edd.  (* [comment removed for export] *)
Definition AF_DCO_CELL      : Z := 0x674b18.  (* [comment removed for export] *)
Definition AGOT_VERBOSITY   : Z := 0x5ae6e8.  (* [comment removed for export] *)
Definition AVERBOSITY_CELL  : Z := 0x706d58.  (* [comment removed for export] *)
Definition ACF_CSMT_CELL    : Z := 0x708e60.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AGOT_DTLS        : Z := 0x5b0698.  (* [comment removed for export] *)
Definition AREAL_TLSGA_CELL : Z := 0x5b17a8.  Definition AREAL_TLSGA : Z := 0x5314b8.  (* [comment removed for export] *)
Definition ACF_ITLS_CELL    : Z := 0x708e71.  (* [comment removed for export] *)
Definition ATSD_CELL        : Z := 0x676b20.  (* [comment removed for export] *)
Definition AMUSL_TSD        : Z := 0xbae5f8.  (* [comment removed for export] *)
Definition AMUSL_DTV        : Z := 0xbae648.  (* [comment removed for export] *)
Definition AMUSL_DTV1       : Z := 0xbae688.   (* [comment removed for export] *)  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMEMCHRP_CELL    : Z := 0x5b16f0.  Definition AREAL_MEMCHR   : Z := 0x5302d0.
Definition AREADP_CELL      : Z := 0x5b1700.  Definition AREAL_READ     : Z := 0x5376f4.
Definition AFWRITEP_CELL    : Z := 0x5b1710.  Definition AREAL_FWRITE   : Z := 0x52be90.
Definition AVPRINTFP_CELL   : Z := 0x5b1738.  Definition AREAL_VPRINTF  : Z := 0x52f268.
Definition AVFPRINTFP_CELL  : Z := 0x5b1740.  Definition AREAL_VFPRINTF : Z := 0x52c10c.
Definition ASTRNLENP_CELL   : Z := 0x5b1878.  Definition AREAL_STRNLEN  : Z := 0x530fa0.
Definition ACF_CHKPRINTF_CELL : Z := 0x708e3c.  (* [comment removed for export] *)
Definition AF_REPGLOB_CELL  : Z := 0x674ad0.  (* [comment removed for export] *)
Definition AMU_GLOBALS_CELL : Z := 0x674b70.  (* [comment removed for export] *)
Definition AREGISTERED_CELL : Z := 0x673c00.  (* [comment removed for export] *)
Definition ACOVFLAG_CELL    : Z := 0x709160.  (* [comment removed for export] *)
Definition ASHW_FMTD        : Z := 0x7fffbb58.  (* [comment removed for export] *)
Definition ASHW_MSG_USAGE   : Z := 0x7fffc250.  (* [comment removed for export] *)
Definition ASHW_MSG_REFUSED : Z := 0x7fffde00.  (* [comment removed for export] *)
Definition ASHW_MSG_OPEN    : Z := 0x7ffff9b0.  (* [comment removed for export] *)
Definition ASHW_MSG_SHORT   : Z := 0x80000838.  (* [comment removed for export] *)
Definition ASHW_STDOUTBUF   : Z := 0x80171e28.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASHW_ERRNO       : Z := 0x8016dcb1.
Definition AREAD_STAGE      : Z := 0xb99910.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASTRRCHRP_CELL   : Z := 0x5b16c8.  Definition AREAL_STRRCHR  : Z := 0x530fe8.   (* [comment removed for export] *)
Definition ASTRSPNP_CELL    : Z := 0x5b16d0.  Definition AREAL_STRSPN   : Z := 0x531028.   (* [comment removed for export] *)
Definition ASTRCPYP_CELL    : Z := 0x5b1870.  Definition AREAL_STRCPY   : Z := 0x530a50.   (* [comment removed for export] *)
Definition ATIMEP_CELL      : Z := 0x5b1728.  Definition AREAL_TIME     : Z := 0x537568.   (* [comment removed for export] *)
Definition ACF_ISTRCHR_CELL : Z := 0x708ee5.  (* [comment removed for export] *)
Definition ACF_ISTRSPN_CELL : Z := 0x708edf.  (* [comment removed for export] *)
Definition AF_REPSTR_CELL   : Z := 0x674ad5.  (* [comment removed for export] *)

(* [comment removed for export] *)

Definition aconst_cells : list (Z * list cell) :=
  [ (AGOT_SHBASE,  [C8 (wz ASHBASE_CELL)]);
    (AGOT_UAR,     [C8 (wz AUAR_CELL)]);
    (AGOT_MEMSETP, [C8 (wz AMEMSETP_CELL)]);
    (AGOT_FLAGS,   [C8 (wz 0x674ab8)]);
    (AGOT_CFLAGS,  [C8 (wz 0x708de8)]);
    (AGOT_HIEND,   [C8 (wz AHIEND_CELL)]);
    (AGOT_MIDBEG,  [C8 (wz AMIDBEG_CELL)]);
    (AGOT_MIDEND,  [C8 (wz AMIDEND_CELL)]);
    (AGOT_SEALED,  [C8 (wz 1)]);
    (AGOT_DYING,   [C8 (wz ADYING_CELL)]);
    (AGOT_PGSZ,    [C8 (wz APGSZ_CELL)]);
    (AGOT_RINTRIN, [C8 (wz ARINTRIN_CELL)]);
    (AGOT_FSTLS,   [C8 (wz 1); C8 (wz 0xfffffffffffff800)]);
    (ASHBASE_CELL, [C8 (wz ASHADOW_BASE)]);
    (AUAR_CELL,    [C4 (wz 1)]);
    (AMEMSETP_CELL,[C8 (wz AREAL_MEMSET)]);
    (AINITED_CELL, [C1 (b8 1); C1 (b8 1)]);          (* [comment removed for export] *)
    (AHIEND_CELL,  [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)]);   (* [comment removed for export] *)
    (ADYING_CELL,  [C4 (wz 0)]);
    (APGSZ_CELL,   [C8 (wz 4096)]);
    (ACANPOISON_CELL, [C1 (b8 1)]);
    (* [comment removed for export] *)
    (AMEMCPYP_CELL, [C8 (wz AREAL_MEMCPY)]);
    (ASTRLENP_CELL, [C8 (wz AREAL_STRLEN)]);
    (ACF_ISTRLEN_CELL, [C1 (b8 1)]);
    (ACF_STRICT_CELL, [C1 (b8 0)]);
    (* [comment removed for export] *)
    (AF_DCO_CELL, [C1 (b8 1)]);
    (AGOT_VERBOSITY, [C8 (wz AVERBOSITY_CELL)]);
    (AVERBOSITY_CELL, [C4 (wz 0)]);
    (ACF_CSMT_CELL, [C8 (wz 0xffffffffffffffff)]);
    (* [comment removed for export] *)
    (AGOT_DTLS, [C8 (wz 0x18)]);
    (AREAL_TLSGA_CELL, [C8 (wz AREAL_TLSGA)]);
    (ACF_ITLS_CELL, [C1 (b8 1)]);
    (ATSD_CELL, [C1 (b8 1)]);
    (ATSD_CELL + 4, [C4 (wz 0)]);
    (AMUSL_TSD, [C8 (wz 0xbcf9f8)]);             (* [comment removed for export] *)
    (AMUSL_DTV, [C8 (wz 0xbae680)]);
    (AMUSL_DTV1, [C8 (wz 0xbaee50)]);
    (* [comment removed for export] *)
    (AMEMCHRP_CELL, [C8 (wz AREAL_MEMCHR)]);
    (AREADP_CELL, [C8 (wz AREAL_READ)]);
    (AFWRITEP_CELL, [C8 (wz AREAL_FWRITE)]);
    (AVPRINTFP_CELL, [C8 (wz AREAL_VPRINTF)]);
    (AVFPRINTFP_CELL, [C8 (wz AREAL_VFPRINTF)]);
    (ASTRNLENP_CELL, [C8 (wz AREAL_STRNLEN)]);
    (ACF_CHKPRINTF_CELL, [C1 (b8 1)]);
    (AF_REPGLOB_CELL, [C4 (wz 1)]);
    (AMU_GLOBALS_CELL, [C8 (wz 0)]);
    (AREGISTERED_CELL, [C8 (wz 1)]);
    (ACOVFLAG_CELL, [C1 (b8 0)]);
    (ASHW_FMTD, [C8 (wz 0)]);
    (ASHW_MSG_USAGE, [C8 (wz 0); C8 (wz 0)]);
    (ASHW_MSG_REFUSED, [C8 (wz 0); C8 (wz 0)]);
    (ASHW_MSG_OPEN, [C8 (wz 0); C8 (wz 0)]);
    (ASHW_MSG_SHORT, [C8 (wz 0); C8 (wz 0)]);
    (ASHW_STDOUTBUF, [C8 (wz 0)]);
    (* [comment removed for export] *)
    (ASTRRCHRP_CELL, [C8 (wz AREAL_STRRCHR)]);
    (ASTRSPNP_CELL, [C8 (wz AREAL_STRSPN)]);
    (ASTRCPYP_CELL, [C8 (wz AREAL_STRCPY)]);
    (ATIMEP_CELL, [C8 (wz AREAL_TIME)]);
    (ACF_ISTRCHR_CELL, [C1 (b8 1)]);
    (ACF_ISTRSPN_CELL, [C1 (b8 1)]);
    (AF_REPSTR_CELL, [C1 (b8 1)]);
    (* [comment removed for export] *)
    (ASHW_ERRNO, [C8 (wz 0)]) ].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aglobals : list (Z * Z * Z) := [
  (* [comment removed for export] *)
  (0xb99910, 65536, 65536)     (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ; (0x49280, 66, 72)   (* [comment removed for export] *)
  ; (0x49560, 24, 24)   (* [comment removed for export] *)
  ; (0x495a0, 23, 24)   (* [comment removed for export] *)
  ; (0x49600, 17, 24)   (* [comment removed for export] *)
  ; (0x49740, 23, 24)   (* [comment removed for export] *)
  ; (0x4a5a0, 25, 32)   (* [comment removed for export] *)
  ; (0x4a660, 24, 24)   (* [comment removed for export] *)
  ; (0x4a860, 20, 24)   (* [comment removed for export] *)
  ; (0x4a8c0, 21, 24)   (* [comment removed for export] *)
  ; (0x4a900, 18, 24)   (* [comment removed for export] *)
  ; (0x4a980, 11, 16)   (* [comment removed for export] *)
  ; (0x4b380, 17, 24)   (* [comment removed for export] *)
  ; (0x4b440, 13, 16)   (* [comment removed for export] *)
  ; (0x4b980, 256, 256)   (* [comment removed for export] *)
  ; (0x4bc60, 14, 16)   (* [comment removed for export] *)
  ; (0x4bc80, 20, 24)   (* [comment removed for export] *)
  ; (0x713a0, 23, 24)   (* [comment removed for export] *)
  ; (0x71b40, 21, 24)   (* [comment removed for export] *)
  ; (0x71b80, 11, 16)   (* [comment removed for export] *)
  ; (0x71ba0, 9, 16)   (* [comment removed for export] *)
  ; (0x71c20, 9, 16)   (* [comment removed for export] *)
  ; (0x71c40, 18, 24)   (* [comment removed for export] *)
  ; (0x71c80, 16, 16)   (* [comment removed for export] *)
  ; (0x737a0, 23, 24)   (* [comment removed for export] *)
  ; (0x73800, 19, 24)   (* [comment removed for export] *)
  ; (0x73b60, 22, 24)   (* [comment removed for export] *)
  ; (0x9bf60, 19, 24)   (* [comment removed for export] *)
  ; (0xb11a0, 24, 24)   (* [comment removed for export] *)
  ; (0xb1220, 27, 32)   (* [comment removed for export] *)
  ; (0xb1260, 27, 32)   (* [comment removed for export] *)
  ; (0xb12a0, 28, 32)   (* [comment removed for export] *)
  ; (0xb1400, 3, 8)   (* [comment removed for export] *)
  ; (0xb1420, 6, 8)   (* [comment removed for export] *)
  ; (0xb1440, 7, 8)   (* [comment removed for export] *)
  ; (0xb1460, 6, 8)   (* [comment removed for export] *)
  ; (0xb1480, 7, 8)   (* [comment removed for export] *)
  ; (0xb14a0, 6, 8)   (* [comment removed for export] *)
  ; (0xb14c0, 7, 8)   (* [comment removed for export] *)
  ; (0xb14e0, 7, 8)   (* [comment removed for export] *)
  ; (0xb1500, 5, 8)   (* [comment removed for export] *)
  ; (0xb1520, 12, 16)   (* [comment removed for export] *)
  ; (0xb1540, 12, 16)   (* [comment removed for export] *)
  ; (0xb1560, 18, 24)   (* [comment removed for export] *)
  ; (0xc44e0, 21, 24)   (* [comment removed for export] *)
  ; (0xc4520, 16, 16)   (* [comment removed for export] *)
  ; (0xc4540, 14, 16)   (* [comment removed for export] *)
  ; (0xc4560, 10, 16)   (* [comment removed for export] *)
  ; (0xc55a0, 20, 24)   (* [comment removed for export] *)
  ; (0xc55e0, 128, 128)   (* [comment removed for export] *)
  ; (0xc5680, 128, 128)   (* [comment removed for export] *)
  ; (0xc7b80, 23, 24)   (* [comment removed for export] *)
  ; (0x119140, 20, 24)   (* [comment removed for export] *)
  ; (0x119180, 24, 24)   (* [comment removed for export] *)
  ; (0x1191c0, 11, 16)   (* [comment removed for export] *)
  ; (0x1191e0, 23, 24)   (* [comment removed for export] *)
  ; (0x119220, 28, 32)   (* [comment removed for export] *)
  ; (0x119260, 67, 72)   (* [comment removed for export] *)
  ; (0x1192e0, 23, 24)   (* [comment removed for export] *)
  ; (0x119320, 21, 24)   (* [comment removed for export] *)
  ; (0x119360, 16, 16)   (* [comment removed for export] *)
  ; (0x119380, 26, 32)   (* [comment removed for export] *)
  ; (0x1193c0, 26, 32)   (* [comment removed for export] *)
  ; (0x119400, 19, 24)   (* [comment removed for export] *)
  ; (0x1194a0, 16, 16)   (* [comment removed for export] *)
  ; (0x1194c0, 21, 24)   (* [comment removed for export] *)
  ; (0x119500, 10, 16)   (* [comment removed for export] *)
  ; (0x119520, 9, 16)   (* [comment removed for export] *)
  ; (0x119540, 9, 16)   (* [comment removed for export] *)
  ; (0x5740c0, 56, 56)   (* [comment removed for export] *)
  ; (0x574320, 360, 360)   (* [comment removed for export] *)
  ; (0x5744e0, 72, 72)   (* [comment removed for export] *)
  ; (0x574560, 160, 160)   (* [comment removed for export] *)
  ; (0x5750a0, 112, 112)   (* [comment removed for export] *)
  ; (0x5ae460, 112, 112)   (* [comment removed for export] *)
  ; (0x5b4000, 8, 8)   (* [comment removed for export] *)
  ; (0x5b4020, 8, 8)   (* [comment removed for export] *)
  ; (0x5b4040, 8, 8)   (* [comment removed for export] *)
  ; (0x5b4080, 8, 8)   (* [comment removed for export] *)
  ; (0xba9940, 1, 8)   (* [comment removed for export] *)
  ; (0xba99e0, 4, 8)   (* [comment removed for export] *)
  ; (0xba9a00, 4, 8)   (* [comment removed for export] *)
  ; (0xba9a20, 1, 8)   (* [comment removed for export] *)
  ; (0xba9a40, 1, 8)   (* [comment removed for export] *)
  ; (0xba9a60, 328, 328)   (* [comment removed for export] *)
  ; (0xba9c00, 4, 8)   (* [comment removed for export] *)
  ; (0xba9c20, 4, 8)   (* [comment removed for export] *)
  ; (0xba9c40, 4, 8)   (* [comment removed for export] *)
  ; (0xba9c60, 4, 8)   (* [comment removed for export] *)
  ; (0xba9c80, 4, 8)   (* [comment removed for export] *)
  ; (0xba9ca0, 4, 8)   (* [comment removed for export] *)
  ; (0xba9cc0, 4, 8)   (* [comment removed for export] *)
  ; (0xba9ce0, 8, 8)   (* [comment removed for export] *)
  ; (0xba9d00, 1, 8)   (* [comment removed for export] *)
  ; (0xba9d20, 8, 8)   (* [comment removed for export] *)
  ; (0xba9d40, 8, 8)   (* [comment removed for export] *)
  ; (0xba9d60, 80, 80)   (* [comment removed for export] *)
  ; (0xba9de0, 1, 8)   (* [comment removed for export] *)
  ; (0xba9e20, 1, 8)   (* [comment removed for export] *)
  ; (0xba9e40, 8, 8)   (* [comment removed for export] *)
  ; (0xba9e60, 8, 8)   (* [comment removed for export] *)
  ; (0xba9e80, 4, 8)   (* [comment removed for export] *)
  ; (0xba9ea0, 1, 8)   (* [comment removed for export] *)
  ; (0xba9ec0, 8, 8)   (* [comment removed for export] *)
  ; (0xba9ee0, 4, 8)   (* [comment removed for export] *)
  ; (0xba9f00, 4, 8)   (* [comment removed for export] *)
  ; (0xba9f20, 4, 8)   (* [comment removed for export] *)
  ; (0xba9f40, 4, 8)   (* [comment removed for export] *)
  ; (0xba9f60, 4, 8)   (* [comment removed for export] *)
  ; (0xba9f80, 1, 8)   (* [comment removed for export] *)
  ; (0xba9fa0, 4, 8)   (* [comment removed for export] *)
  ; (0xba9fc0, 1, 8)   (* [comment removed for export] *)
  ; (0xba9fe0, 4, 8)   (* [comment removed for export] *)
  ; (0xbaa000, 1, 8)   (* [comment removed for export] *)
  ; (0xbaa020, 4, 8)   (* [comment removed for export] *)
  ; (0xbaa040, 4, 8)   (* [comment removed for export] *)
  ; (0xbaa060, 8, 8)   (* [comment removed for export] *)
  ; (0xbaa080, 4, 8)   (* [comment removed for export] *)
  ; (0xbaa0a0, 4, 8)   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ; (0x4b620, 17, 24)   (* [comment removed for export] *)
  ; (0x4b660, 9, 16)   (* [comment removed for export] *)
  ; (0x4b680, 8, 8)   (* [comment removed for export] *)
  ; (0x4b6a0, 5, 8)   (* [comment removed for export] *)
  ; (0x4b6c0, 7, 8)   (* [comment removed for export] *)
  ; (0x4b6e0, 6, 8)   (* [comment removed for export] *)
  ; (0x4b700, 10, 16)   (* [comment removed for export] *)
  ; (0x4b720, 4, 8)   (* [comment removed for export] *)
  ; (0x4b740, 3, 8)   (* [comment removed for export] *)
  ; (0x4b760, 11, 16)   (* [comment removed for export] *)
  ; (0x4bd80, 5, 8)   (* [comment removed for export] *)
  ; (0x4bda0, 7, 8)   (* [comment removed for export] *)
  ; (0xf8b80, 16, 16)   (* [comment removed for export] *)
  ; (0x538b60, 704, 704)   (* [comment removed for export] *)
  ; (0x538ec0, 640, 640)   (* [comment removed for export] *)
  ; (0x5391e0, 48, 48)   (* [comment removed for export] *)
  ; (0x5a53c0, 320, 320)   (* [comment removed for export] *)
  ; (0x5a5540, 368, 368)   (* [comment removed for export] *)
  ; (0x5a5700, 1312, 1312)   (* [comment removed for export] *)
  ; (0x5a5d60, 512, 512)   (* [comment removed for export] *)
  ; (0x5a5fe0, 2016, 2016)   (* [comment removed for export] *)
  ; (0x5a69a0, 64, 64)   (* [comment removed for export] *)
  ; (0x5a6a00, 560, 560)   (* [comment removed for export] *)
  ; (0x5a6cc0, 272, 272)   (* [comment removed for export] *)
  ; (0x5a6e20, 768, 768)   (* [comment removed for export] *)
  ; (0x5a71e0, 1888, 1888)   (* [comment removed for export] *)
  ; (0x5a7b00, 448, 448)   (* [comment removed for export] *)
  ; (0x5a7d20, 512, 512)   (* [comment removed for export] *)
  ; (0x5a7fa0, 176, 176)   (* [comment removed for export] *)
  ; (0x5a8080, 1232, 1232)   (* [comment removed for export] *)
  ; (0x5a8680, 768, 768)   (* [comment removed for export] *)
  ; (0x5a8a40, 624, 624)   (* [comment removed for export] *)
  ; (0x5a8d40, 1184, 1184)   (* [comment removed for export] *)
  ; (0x5a9300, 368, 368)   (* [comment removed for export] *)
  ; (0x5a94c0, 736, 736)   (* [comment removed for export] *)
  ; (0x5a9840, 272, 272)   (* [comment removed for export] *)
  ; (0x5a99a0, 640, 640)   (* [comment removed for export] *)
  ; (0x5a9cc0, 528, 528)   (* [comment removed for export] *)
  ; (0x5a9f60, 416, 416)   (* [comment removed for export] *)
  ; (0x5aa160, 224, 224)   (* [comment removed for export] *)
  ; (0x5aa260, 1648, 1648)   (* [comment removed for export] *)
  ; (0x5aaa60, 496, 496)   (* [comment removed for export] *)
  ; (0x5aacc0, 1712, 1712)   (* [comment removed for export] *)
  ; (0x5ab520, 288, 288)   (* [comment removed for export] *)
  ; (0x5ab680, 160, 160)   (* [comment removed for export] *)
  ; (0x5ab740, 80, 80)   (* [comment removed for export] *)
  ; (0x5ab7c0, 240, 240)   (* [comment removed for export] *)
  ; (0x5ab8e0, 416, 416)   (* [comment removed for export] *)
  ; (0x5abae0, 192, 192)   (* [comment removed for export] *)
  ; (0x5abbc0, 2576, 2576)   (* [comment removed for export] *)
  ; (0x5b4060, 4, 8)   (* [comment removed for export] *)
  ; (0xf8ba0, 32, 32)   (* [comment removed for export] *)
  (* [comment removed for export] *)
  ].

(* [comment removed for export] *)
Definition global_shadow (sz szrz : Z) : list byte :=
  shadow_of sz ++ poison_bytes (Z.to_nat ((szrz - 8 * nsh sz) / 8)) 0xf9.

Definition AGLOBAL_SH (m : mem) (g : Z * Z * Z) : Prop :=
  let '(beg, sz, szrz) := g in SHAD m beg (global_shadow sz szrz).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ACONST (m : mem) : Prop :=
  Forall (fun ac => rw_cells asegs m (fst ac) (snd ac)) aconst_cells
  /\ Forall (AGLOBAL_SH m) aglobals
  /\ stk asegs m (sh AIMG_LO) (sh AIMG_TOP).

(* [comment removed for export] *)
Definition aconst_addr (a : Z) : Prop :=
  (0x538000 <= a < 0x5b18d8)                                   (* [comment removed for export] *)
  \/ (ASHBASE_CELL <= a < ASHBASE_CELL + 12) \/ (AMEMCPYP_CELL <= a < AMEMCPYP_CELL + 16)
  \/ (AINITED_CELL <= a < AINITED_CELL + 2) \/ (AHIEND_CELL <= a < AHIEND_CELL + 24)
  \/ (ADYING_CELL <= a < ADYING_CELL + 4) \/ (APGSZ_CELL <= a < APGSZ_CELL + 8)
  \/ (ACANPOISON_CELL <= a < ACANPOISON_CELL + 1) \/ (0x708de8 <= a < 0x708f14)
  \/ (0x674ab8 <= a < 0x674b78) \/ (AVERBOSITY_CELL <= a < AVERBOSITY_CELL + 4)   (* [comment removed for export] *)
  \/ (AREAL_TLSGA_CELL <= a < AREAL_TLSGA_CELL + 8) \/ (ATSD_CELL <= a < ATSD_CELL + 8) \/ (0xbae5f8 <= a < 0xbae690)   (* [comment removed for export] *)
  \/ (AREGISTERED_CELL <= a < AREGISTERED_CELL + 8) \/ (ACOVFLAG_CELL <= a < ACOVFLAG_CELL + 1)   (* [comment removed for export] *)
  \/ (sh AIMG_LO <= a < sh AIMG_TOP).

(* [comment removed for export] *)
Definition aconst_ok (iv : Z * Z) : Prop := forall a, fst iv <= a < snd iv -> ~ aconst_addr a.

Lemma aconst_ok_intro : forall lo hi,
  (hi <= 0x538000 \/ 0x5b18d8 <= lo) ->
  (hi <= ASHBASE_CELL \/ ASHBASE_CELL + 12 <= lo) -> (hi <= AMEMCPYP_CELL \/ AMEMCPYP_CELL + 16 <= lo) ->
  (hi <= AINITED_CELL \/ AINITED_CELL + 2 <= lo) -> (hi <= AHIEND_CELL \/ AHIEND_CELL + 24 <= lo) ->
  (hi <= ADYING_CELL \/ ADYING_CELL + 4 <= lo) -> (hi <= APGSZ_CELL \/ APGSZ_CELL + 8 <= lo) ->
  (hi <= ACANPOISON_CELL \/ ACANPOISON_CELL + 1 <= lo) -> (hi <= 0x708de8 \/ 0x708f14 <= lo) ->
  (hi <= 0x674ab8 \/ 0x674b78 <= lo) -> (hi <= AVERBOSITY_CELL \/ AVERBOSITY_CELL + 4 <= lo) ->
  (hi <= AREAL_TLSGA_CELL \/ AREAL_TLSGA_CELL + 8 <= lo) -> (hi <= ATSD_CELL \/ ATSD_CELL + 8 <= lo) -> (hi <= 0xbae5f8 \/ 0xbae690 <= lo) ->
  (hi <= AREGISTERED_CELL \/ AREGISTERED_CELL + 8 <= lo) -> (hi <= ACOVFLAG_CELL \/ ACOVFLAG_CELL + 1 <= lo) ->
  (hi <= sh AIMG_LO \/ sh AIMG_TOP <= lo) ->
  aconst_ok (lo, hi).
Proof.
  intros lo hi K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K13 K14 K15 K16 K17 K12 a Ha K. cbn in Ha. unfold aconst_addr in K.
  destruct K as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]]]]];
    [ clear -K1 Ha K | clear -K2 Ha K | clear -K3 Ha K | clear -K4 Ha K | clear -K5 Ha K | clear -K6 Ha K
    | clear -K7 Ha K | clear -K8 Ha K | clear -K9 Ha K | clear -K10 Ha K | clear -K11 Ha K | clear -K13 Ha K | clear -K14 Ha K | clear -K15 Ha K
    | clear -K16 Ha K | clear -K17 Ha K | clear -K12 Ha K ]; lia.
Qed.

(* [comment removed for export] *)
Lemma aconst_ok_high : forall lo hi, sh AIMG_TOP <= lo ->
  (hi <= 0x538000 \/ 0xbcff30 <= lo
   \/ (0xb99910 <= lo /\ hi <= 0xbae5f8) \/ (0xbae680 <= lo /\ hi <= 0xbcf9f8) \/ (0xbcfa00 <= lo /\ hi <= 0xbcff30)) ->   (* [comment removed for export] *)
  aconst_ok (lo, hi).
Proof.
  intros lo hi H1 H2. apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AF_DCO_CELL, AVERBOSITY_CELL,
    AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *; try lia.
Qed.

(* [comment removed for export] *)
Lemma aconst_cells_in_addr :
  Forall (fun ac => forall x, fst ac <= x < fst ac + Z.of_nat (cells_size (snd ac)) -> aconst_addr x) aconst_cells.
Proof.
  unfold aconst_cells, aconst_addr, AGOT_SHBASE, AGOT_UAR, AGOT_MEMSETP, AGOT_FLAGS, AGOT_CFLAGS, AGOT_HIEND, AGOT_MIDBEG, AGOT_MIDEND, AGOT_SEALED,
    AGOT_DYING, AGOT_PGSZ, AGOT_RINTRIN, AGOT_FSTLS, ASHBASE_CELL, AUAR_CELL, AMEMSETP_CELL, AINITED_CELL, ARINTRIN_CELL, AHIEND_CELL,
    AMIDBEG_CELL, AMIDEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AMEMCPYP_CELL, ASTRLENP_CELL, ACF_ISTRLEN_CELL, ACF_STRICT_CELL,
    AF_DCO_CELL, AGOT_VERBOSITY, AVERBOSITY_CELL, ACF_CSMT_CELL,
    AGOT_DTLS, AREAL_TLSGA_CELL, AREAL_TLSGA, ACF_ITLS_CELL, ATSD_CELL, AMUSL_TSD, AMUSL_DTV, AMUSL_DTV1,
    AMEMCHRP_CELL, AREADP_CELL, AFWRITEP_CELL, AVPRINTFP_CELL, AVFPRINTFP_CELL, ASTRNLENP_CELL, ACF_CHKPRINTF_CELL, AF_REPGLOB_CELL,
    AMU_GLOBALS_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, ASHW_FMTD, ASHW_MSG_USAGE, ASHW_MSG_REFUSED, ASHW_MSG_OPEN, ASHW_MSG_SHORT, ASHW_STDOUTBUF,
    ASTRRCHRP_CELL, AREAL_STRRCHR, ASTRSPNP_CELL, AREAL_STRSPN, ASTRCPYP_CELL, AREAL_STRCPY, ATIMEP_CELL, AREAL_TIME, ACF_ISTRCHR_CELL, ACF_ISTRSPN_CELL, AF_REPSTR_CELL,
    ASHW_ERRNO, sh, AIMG_LO, AIMG_TOP.
  rewrite ?ASHADOW_BASE_val.
  repeat (constructor; [cbn; intros; lia|]). constructor.
Qed.

Lemma global_shadow_length : forall sz szrz, 0 <= sz -> 8 * nsh sz <= szrz ->
  Z.of_nat (length (global_shadow sz szrz)) = nsh sz + (szrz - 8 * nsh sz) / 8.
Proof.
  intros sz szrz H1 H2. unfold global_shadow, poison_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length by lia.
  rewrite Z2Nat.id; [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition aglobal_chk (g : Z * Z * Z) : bool :=
  let '(beg, sz, szrz) := g in
  ((AIMG_LO <=? beg) && (beg + szrz <=? AIMG_TOP) && (0 <=? sz) && (8 * nsh sz <=? szrz) && (szrz mod 8 =? 0) && (beg mod 8 =? 0))%bool.
Lemma aglobal_chk_ok : forall g : Z * Z * Z, aglobal_chk g = true ->
  let '(beg, sz, szrz) := g in
     AIMG_LO <= beg /\ beg + szrz <= AIMG_TOP /\ 0 <= sz /\ 8 * nsh sz <= szrz /\ szrz mod 8 = 0 /\ beg mod 8 = 0.
Proof.
  intros [[beg sz] szrz] H. unfold aglobal_chk in H.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  repeat split; first [apply Z.leb_le; assumption | apply Z.eqb_eq; assumption].
Qed.

(* [comment removed for export] *)
Lemma aglobals_facts :
  Forall (fun g : Z * Z * Z => let '(beg, sz, szrz) := g in
     AIMG_LO <= beg /\ beg + szrz <= AIMG_TOP /\ 0 <= sz /\ 8 * nsh sz <= szrz /\ szrz mod 8 = 0 /\ beg mod 8 = 0) aglobals.
Proof. apply Forall_forall. intros g Hg. apply aglobal_chk_ok. exact (proj1 (forallb_forall aglobal_chk aglobals) eq_refl g Hg). Qed.

(* [comment removed for export] *)
Lemma ACONST_ext : forall m m',
  ACONST m ->
  (forall a, 0 <= a < 2^64 -> aconst_addr a -> m' (wa a) = m (wa a)) ->
  (forall a, 0 <= a < 2^64 -> wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None) ->
  (forall a, sh AIMG_LO <= a < sh AIMG_TOP -> exists b, mrd asegs m' (wa a) = Some b) ->
  ACONST m'.
Proof.
  intros m m' (C1 & C2 & C3) EQ WM RD. split; [|split].
  - apply Forall_forall. intros [a cs] IN. pose proof (proj1 (Forall_forall _ _) C1 _ IN) as RC. cbn in RC |- *.
    assert (R : forall x, a <= x < a + Z.of_nat (cells_size cs) -> aconst_addr x).
    { exact (proj1 (Forall_forall _ _) aconst_cells_in_addr _ IN). }
    destruct RC as [[WF BA] WR]. split; [split; [exact WF|]|].
    + destruct BA as (B0 & B1 & BB). split; [exact B0|]. split; [exact B1|]. intros i Hi. unfold mrd. rewrite EQ; [| lia |].
      * apply BB. exact Hi.
      * apply R. rewrite cells_bytes_length in Hi by exact WF. lia.
    + destruct WR as (W0 & W1 & WW). split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM; [lia|]. apply WW. exact Hi.
  - apply Forall_forall. intros [[beg sz] szrz] IN. pose proof (proj1 (Forall_forall _ _) C2 _ IN) as G. cbn in G |- *.
    destruct G as (G0 & G1 & [GB GW]). split; [exact G0|]. split; [exact G1|].
    assert (R : forall x, sh beg <= x < sh beg + Z.of_nat (length (global_shadow sz szrz)) -> aconst_addr x).
    { intros x Hx. unfold aconst_addr. do 16 right.
      pose proof (proj1 (Forall_forall _ _) aglobals_facts _ IN) as IMG. cbn in IMG. destruct IMG as (I1 & I2 & I4 & I5 & I6 & I7).
      rewrite global_shadow_length in Hx by lia.
      unfold sh, nsh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. }
    split.
    + destruct GB as (B0 & B1 & BB). split; [exact B0|]. split; [exact B1|]. intros i Hi. unfold mrd. rewrite EQ; [| lia |].
      * apply BB. exact Hi.
      * apply R. lia.
    + destruct GW as (W0 & W1 & WW). split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM; [lia|]. apply WW. exact Hi.
  - destruct C3 as (S0 & S1 & SS). split; [exact S0|]. split; [exact S1|]. intros a Ha. split.
    + apply WM; [unfold sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *; lia|]. apply (proj1 (SS a Ha)).
    + apply RD. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma ACONST_frame : forall W m m',
  ACONST m -> munch W m m' -> wmono asegs m m' -> Forall aconst_ok W -> ACONST m'.
Proof.
  intros W m m' AC MU WM FW.
  assert (OUT : forall a, aconst_addr a -> outside W a).
  { intros a Ha. clear MU WM AC. induction W as [|[lo hi] W IH]; [exact I|]. cbn. split.
    - intros K. exact (Forall_inv FW a K Ha).
    - apply IH. exact (Forall_inv_tail FW). }
  eapply ACONST_ext; [exact AC | | intros a _ HW; apply WM; exact HW |].
  - intros a Ha HC. unfold wa. apply MU. rewrite unsigned_lit by lia. apply OUT. exact HC.
  - intros a Ha. destruct AC as (_ & _ & (S0 & S1 & SS)). destruct (SS a Ha) as [W0 (b & Hb)].
    unfold mrd in *. unfold wa in *. rewrite MU.
    + rewrite Hb. eauto.
    + rewrite unsigned_lit by (unfold sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *; lia). apply OUT. unfold aconst_addr. do 16 right. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ACONST_cell : forall m a cs, ACONST m -> In (a, cs) aconst_cells -> rw_cells asegs m a cs.
Proof. intros m a cs (C & _ & _) IN. exact (proj1 (Forall_forall _ _) C _ IN). Qed.

(* [comment removed for export] *)
Lemma ACONST_shbase : forall m, ACONST m ->
  rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] /\ rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)].
Proof. intros m AC. split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.

(* [comment removed for export] *)
Lemma ACONST_uar : forall m, ACONST m ->
  rw_cells asegs m AGOT_UAR [C8 (wz AUAR_CELL)] /\ rw_cells asegs m AUAR_CELL [C4 (wz 1)].
Proof. intros m AC. split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.

Lemma ACONST_memsetp : forall m, ACONST m ->
  rw_cells asegs m AGOT_MEMSETP [C8 (wz AMEMSETP_CELL)] /\ rw_cells asegs m AMEMSETP_CELL [C8 (wz AREAL_MEMSET)].
Proof. intros m AC. split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.

Lemma ACONST_memcpyp : forall m, ACONST m -> rw_cells asegs m AMEMCPYP_CELL [C8 (wz AREAL_MEMCPY)].
Proof. intros m AC. eapply ACONST_cell; [exact AC| in_nth]. Qed.
Lemma ACONST_strlenp : forall m, ACONST m -> rw_cells asegs m ASTRLENP_CELL [C8 (wz AREAL_STRLEN)].
Proof. intros m AC. eapply ACONST_cell; [exact AC| in_nth]. Qed.
Lemma ACONST_cflags : forall m, ACONST m ->
  rw_cells asegs m ACF_ISTRLEN_CELL [C1 (b8 1)] /\ rw_cells asegs m ACF_STRICT_CELL [C1 (b8 0)].
Proof. intros m AC. split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.

Lemma ACONST_annot : forall m, ACONST m ->
  rw_cells asegs m AF_DCO_CELL [C1 (b8 1)] /\ rw_cells asegs m AGOT_VERBOSITY [C8 (wz AVERBOSITY_CELL)]
  /\ rw_cells asegs m AVERBOSITY_CELL [C4 (wz 0)] /\ rw_cells asegs m ACF_CSMT_CELL [C8 (wz 0xffffffffffffffff)].
Proof. intros m AC. repeat split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.

Lemma ACONST_global : forall m beg sz szrz, ACONST m -> In (beg, sz, szrz) aglobals ->
  SHAD m beg (global_shadow sz szrz).
Proof. intros m beg sz szrz (_ & C & _) IN. exact (proj1 (Forall_forall _ _) C _ IN). Qed.

(* [comment removed for export] *)
Lemma ACONST_global_addressable : forall m beg sz szrz, ACONST m -> In (beg, sz, szrz) aglobals -> 0 <= sz ->
  addressable m beg sz.
Proof.
  intros m beg sz szrz AC IN Hsz. pose proof (ACONST_global m beg sz szrz AC IN) as G.
  unfold global_shadow in G. apply SHAD_app in G. destruct G as [G _]. split; [exact Hsz| exact G].
Qed.

(* [comment removed for export] *)
Lemma ACONST_drv_reals : forall m, ACONST m ->
  rw_cells asegs m AMEMCHRP_CELL [C8 (wz AREAL_MEMCHR)] /\ rw_cells asegs m AREADP_CELL [C8 (wz AREAL_READ)]
  /\ rw_cells asegs m AFWRITEP_CELL [C8 (wz AREAL_FWRITE)] /\ rw_cells asegs m AVPRINTFP_CELL [C8 (wz AREAL_VPRINTF)]
  /\ rw_cells asegs m AVFPRINTFP_CELL [C8 (wz AREAL_VFPRINTF)] /\ rw_cells asegs m ASTRNLENP_CELL [C8 (wz AREAL_STRNLEN)].
Proof. intros m AC. repeat split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.
Lemma ACONST_drv_flags : forall m, ACONST m ->
  rw_cells asegs m ACF_CHKPRINTF_CELL [C1 (b8 1)] /\ rw_cells asegs m AF_REPGLOB_CELL [C4 (wz 1)]
  /\ rw_cells asegs m AMU_GLOBALS_CELL [C8 (wz 0)] /\ rw_cells asegs m AREGISTERED_CELL [C8 (wz 1)]
  /\ rw_cells asegs m ACOVFLAG_CELL [C1 (b8 0)]
  /\ rw_cells asegs m AINITED_CELL [C1 (b8 1); C1 (b8 1)] /\ rw_cells asegs m ACANPOISON_CELL [C1 (b8 1)]
  /\ rw_cells asegs m ACF_CSMT_CELL [C8 (wz 0xffffffffffffffff)] /\ rw_cells asegs m AMEMSETP_CELL [C8 (wz AREAL_MEMSET)]
  /\ rw_cells asegs m AMEMCPYP_CELL [C8 (wz AREAL_MEMCPY)] /\ rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)].
Proof. intros m AC. repeat split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.
Lemma ACONST_drv_shwords : forall m, ACONST m ->
  rw_cells asegs m ASHW_FMTD [C8 (wz 0)] /\ rw_cells asegs m ASHW_MSG_USAGE [C8 (wz 0); C8 (wz 0)]
  /\ rw_cells asegs m ASHW_MSG_REFUSED [C8 (wz 0); C8 (wz 0)] /\ rw_cells asegs m ASHW_MSG_OPEN [C8 (wz 0); C8 (wz 0)]
  /\ rw_cells asegs m ASHW_MSG_SHORT [C8 (wz 0); C8 (wz 0)] /\ rw_cells asegs m ASHW_STDOUTBUF [C8 (wz 0)].
Proof. intros m AC. repeat split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.
(* [comment removed for export] *)
Lemma ACONST_icpt : forall m, ACONST m ->
  rw_cells asegs m ASTRRCHRP_CELL [C8 (wz AREAL_STRRCHR)] /\ rw_cells asegs m ASTRSPNP_CELL [C8 (wz AREAL_STRSPN)]
  /\ rw_cells asegs m ASTRCPYP_CELL [C8 (wz AREAL_STRCPY)] /\ rw_cells asegs m ATIMEP_CELL [C8 (wz AREAL_TIME)]
  /\ rw_cells asegs m ACF_ISTRCHR_CELL [C1 (b8 1)] /\ rw_cells asegs m ACF_ISTRSPN_CELL [C1 (b8 1)] /\ rw_cells asegs m AF_REPSTR_CELL [C1 (b8 1)].
Proof. intros m AC. repeat split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.
(* [comment removed for export] *)
Lemma ACONST_errno_shw : forall m, ACONST m -> rw_cells asegs m ASHW_ERRNO [C8 (wz 0)].
Proof. intros m AC. eapply ACONST_cell; [exact AC| in_nth]. Qed.
Lemma ACONST_errno_accessible : forall m, ACONST m -> accessible m 0xbae588 64.
Proof.
  intros m AC. pose proof (ACONST_errno_shw m AC) as RC.
  assert (AD : addressable m 0xbae588 64).
  { split; [lia|]. apply (SHAD_of_rw_cells m 0xbae588 8); [lia| reflexivity|].
    pose proof (rw_cells_merge asegs m ASHW_ERRNO [] [C8 (wz 0)] []) as M. cbn [app cells_size csize cells_bytes] in M.
    unfold ASHW_ERRNO in M. change (sh 0xbae588) with 0x8016dcb1.
    replace (shadow_of 64) with (cbytes (C8 (wz 0)) ++ []) by (vm_compute; reflexivity). apply M. exact RC. }
  eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia].
Qed.
(* [comment removed for export] *)
Lemma ACONST_read_stage : forall m, ACONST m -> addressable m AREAD_STAGE 65536.
Proof. intros m AC. apply (ACONST_global_addressable m AREAD_STAGE 65536 65536 AC); [in_nth | lia]. Qed.

Lemma ACONST_imgvis : forall m, ACONST m -> stk asegs m (sh AIMG_LO) (sh AIMG_TOP).
Proof. intros m (_ & _ & S). exact S. Qed.

(* [comment removed for export] *)
Lemma ACONST_shvis : forall m lo hi, ACONST m -> AIMG_LO + 64 <= lo -> lo <= hi -> hi + 64 <= AIMG_TOP -> shvis m lo hi.
Proof.
  intros m lo hi AC H1 H2 H3. pose proof (ACONST_imgvis m AC) as (S0 & S1 & SS).
  pose proof (hull_lo_le lo ltac:(unfold AIMG_LO in *; lia)) as HL. pose proof (hull_hi_ge hi ltac:(unfold AIMG_LO in *; lia)) as HH.
  assert (L1 : sh AIMG_LO <= sh (hull_lo lo)) by (apply sh_mono; lia).
  assert (L2 : sh (hull_hi hi) <= sh AIMG_TOP) by (apply sh_mono; lia).
  split; [lia|]. split; [lia|]. intros a Ha. apply SS. lia.
Qed.
