(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts Globals IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptLeaves I_printf_back IcptPack IcptPack2.

Definition IC_all {HC : HasCeiling} : icpt_contracts :=
  mkIC ic_strlen_proof ic_strncmp_proof ic_strncasecmp_proof ic_memchr_proof ic_memcpy_proof ic_memcpy_i_proof ic_memmove_proof
       ic_memset_proof ic_memset_i_proof ic_tolower_proof ic_htons_proof ic_errno_location_proof
       ic_read_front_proof ic_read_back_proof ic_fwrite_front_proof ic_fwrite_back_proof
       ic_vprintf_front_proof ic_vprintf_back_proof ic_vfprintf_front_proof ic_vfprintf_back_proof
       (ic_fprintf_s_front_proof 88517%Z 17%Z) (ic_fprintf_s_front_proof 121494%Z 21%Z) (ic_fprintf_s_front_proof 121515%Z 23%Z)
       ic_fprintf_u_front_proof ic_fprintf_back_proof ic_asan_dtor_proof
       ic_strtol_proof ic_sscanf_status_proof ic_strncpy_proof ic_atoi_proof ic_inet_pton_proof ic_strtol0_proof
       ic_strstr_chunked_proof ic_strtoll_proof ic_sscanf_version_proof.
Print Assumptions IC_all.
